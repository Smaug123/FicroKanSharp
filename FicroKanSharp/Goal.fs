namespace FicroKanSharp

open FicroKanSharp

[<RequireQualifiedAccess>]
[<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module Goal =
    let callFresh (f : Variable -> Goal) = Goal.Fresh f

    let delay (g : unit -> Goal) = Goal.Fresh (fun _ -> g ())

    /// Boolean "or": either goal must be satisfied.
    let disj (goal1 : Goal) (goal2 : Goal) : Goal = Goal.Disj (goal1, goal2)

    /// Boolean "and": both goals must be satisfied simultaneously.
    let conj (goal1 : Goal) (goal2 : Goal) : Goal = Goal.Conj (goal1, goal2)

    let equiv (term1 : Term) (term2 : Term) : Goal = Goal.Equiv (term1, term2)

    let never : Goal =
        equiv (Term.Symbol ("_never", [])) (Term.Symbol ("_never2", []))

    let always : Goal =
        equiv (Term.Symbol ("_always", [])) (Term.Symbol ("_always", []))

    let all (goals : Goal list) : Goal =
        match goals with
        | [] -> always
        | goal :: goals -> goals |> List.fold conj goal

    let any (goals : Goal list) : Goal =
        match goals with
        | [] -> never
        | goal :: goals -> goals |> List.fold disj goal

    let private walk (u : Term) (s : State) : Term =
        match u with
        | Term.Variable u as x ->
            match Map.tryFind u s.Substitution with
            | None -> x
            | Some subst -> subst
        | u -> u

    let private extend (v : Variable) (t : Term) (s : State) =
        { s with
            Substitution = Map.add v t s.Substitution
        }

    let rec private unifyList (args1 : _) (args2 : _) (state : State) : State option =
        match args1, args2 with
        | [], [] -> Some state
        | _, []
        | [], _ -> None
        | arg1 :: args1, arg2 :: args2 ->

        match unify arg1 arg2 state with
        | None -> None
        | Some state -> unifyList args1 args2 state

    and private unify (u : Term) (v : Term) (s : State) : State option =
        let u = walk u s
        let v = walk v s

        match u, v with
        | Term.Variable u, Term.Variable v when u = v -> s |> Some
        | Term.Variable u, v -> extend u v s |> Some
        | u, Term.Variable v -> extend v u s |> Some
        | Term.Symbol (name1, args1), Term.Symbol (name2, args2) ->
            if name1.GetType().ReflectedType <> name2.GetType().ReflectedType then
                None
            else
                let ty = name1.GetType().ReflectedType
                let name2 = unbox name2

                let customUnification () =
                    // Custom unification rules
                    let unifyMethod =
                        ty.GetMethod("Unify", System.Reflection.BindingFlags.Public ||| System.Reflection.BindingFlags.Static)

                    if obj.ReferenceEquals (unifyMethod, null) then
                        // Custom unification fails because the user didn't provide any unification rules
                        None
                    else
            //(unify : Term -> Term -> bool option)
                        if unifyMethod.ReturnParameter.ParameterType <> typeof<State option> then
                            failwith $"Incorrect unify return parameter should have been Option<State>: {unifyMethod.ReturnParameter.ParameterType}"
                        match unifyMethod.GetParameters () with
                        | [| unifyParam ; name1Param ; args1Param ; name2Param ; args2Param ; stateParam |] ->
                            let result = unifyMethod.Invoke (name1, [| unify; name1; args1; name2; args2; s|]) |> unbox<State option>
                            result
                        | parameters ->
                            failwith $"Incorrect unify parameters: {parameters |> Array.toList}"

                if name1 = name2 && args1.Length = args2.Length then
                    // Structural unification succeeds
                    match unifyList args1 args2 s with
                    | Some s -> Some s
                    | None ->
                        customUnification ()
                else
                    customUnification ()

        | _, _ -> None

    let rec private evaluate' (goal : Goal) (state : State) : Stream =
        match goal with
        | Goal.Equiv (t1, t2) ->
            match unify t1 t2 state with
            | None -> Stream.empty
            | Some unification -> Stream.Nonempty (unification, Stream.empty)
        | Goal.Fresh goal ->
            let newVar = state.VariableCounter

            Stream.Procedure (fun () ->
                evaluate'
                    (goal newVar)
                    { state with
                        VariableCounter = Variable.incr state.VariableCounter
                    }
            )
        | Goal.Disj (goal1, goal2) -> Stream.union (evaluate' goal1 state) (evaluate' goal2 state)
        | Goal.Conj (goal1, goal2) -> Stream.bind (evaluate' goal1 state) (evaluate' goal2)

    let evaluate (goal : Goal) = evaluate' goal State.empty
