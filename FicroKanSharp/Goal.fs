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
            if name1.GetType () <> name2.GetType () then
                None
            else
                let name2 = unbox name2

                if (name1 <> name2) || (args1.Length <> args2.Length) then
                    None
                else
                    unifyList args1 args2 s

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
