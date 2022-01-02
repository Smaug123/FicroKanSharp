namespace FicroKanSharp

open FicroKanSharp
open FSharp.Reflection

[<RequireQualifiedAccess>]
[<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module Goal =
    let callFresh (f : Variable -> Goal) = Goal.Fresh f

    let delay (g : unit -> Goal) =
        // This could be expressed as `Goal.Fresh (fun _ -> g ())`,
        // but I prefer slightly bloating the core rather than bloating all
        // the unification output.
        Goal.Delay g

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

    // TODO(perf): return a new state where we've propagated
    // the unification
    let rec private walk (u : Term) (s : State) : Term =
        match u with
        | Term.Variable u as x ->
            match Map.tryFind u s.Substitution with
            | None -> x
            | Some subst -> walk subst s
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

    and private customUnification<'a>
        (ty : System.Type)
        (name1 : 'a)
        (args1 : Term list)
        (name2 : 'a)
        (args2 : Term list)
        (state : State)
        =
        // Custom unification rules
        let unifyMethod =
            ty.GetMethod (
                "Unify",
                System.Reflection.BindingFlags.Static
                ||| System.Reflection.BindingFlags.Public
                ||| System.Reflection.BindingFlags.FlattenHierarchy
                ||| System.Reflection.BindingFlags.NonPublic
            )

        if obj.ReferenceEquals (unifyMethod, null) then
            // Custom unification fails because the user didn't provide any unification rules
            None
        else
        //(unify : Term -> Term -> bool option)
        if unifyMethod.ReturnParameter.ParameterType
           <> typeof<State option> then
            failwith
                $"Incorrect unify return parameter should have been Option<State>: {unifyMethod.ReturnParameter.ParameterType}"

        match unifyMethod.GetParameters () with
        | [| unifyParam ; _name1Param ; args1Param ; _name2Param ; args2Param ; stateParam |] ->
            let wrongParams =
                [
                    let t =
                        typeof<Term -> Term -> State -> State option>

                    if unifyParam.ParameterType <> t then
                        yield nameof unifyParam, t

                    let t = typeof<Term list>

                    if args1Param.ParameterType <> t then
                        yield nameof args1Param, t

                    if args2Param.ParameterType <> t then
                        yield nameof args2Param, t

                    let t = typeof<State>

                    if stateParam.ParameterType <> t then
                        yield nameof stateParam, t
                ]

            match wrongParams with
            | [] -> ()
            | wrongParams ->
                let wrongParams =
                    wrongParams
                    |> List.map (fun (s, ty) -> $"{s} (expected: {ty.Name})")
                    |> String.concat "; "

                failwith $"Wrong parameters on Unify method of type {ty.Name}: {wrongParams}"

            let result =
                unifyMethod.Invoke (
                    name1,
                    [|
                        unify
                        name1
                        args1
                        name2
                        args2
                        state
                    |]
                )
                |> unbox<State option>

            result
        | parameters -> failwith $"Incorrect unify parameters: {parameters |> Array.toList}"


    and private unify (uIn : Term) (vIn : Term) (s : State) : State option =
        let u = walk uIn s
        let v = walk vIn s

        match u, v with
        | Term.Variable u, Term.Variable v when u = v -> s |> Some
        | Term.Variable u, v -> extend u v s |> Some
        | u, Term.Variable v -> extend v u s |> Some
        | Term.Symbol (name1, args1), Term.Symbol (name2, args2) ->
            let ty =
                name1.GetType ()
                |> fun ty ->
                    if FSharpType.IsUnion ty then
                        if FSharpType.GetUnionCases ty
                           |> Array.forall (fun i -> i.GetFields().Length = 0) then
                            // reference enum
                            ty
                        else
                            ty.DeclaringType
                    else
                        ty

            if not <| name2.GetType().IsAssignableTo ty then
                None
            else
                let name2 = unbox name2

                if name1 = name2 && args1.Length = args2.Length then
                    match unifyList args1 args2 s with
                    | Some s ->
                        // Structural unification succeeds
                        Some s
                    | None -> customUnification ty name1 args1 name2 args2 s
                else
                    customUnification ty name1 args1 name2 args2 s

        | _, _ -> None

    let rec private evaluate' (debug : bool) (goal : Goal) (state : State) : Stream =
        if debug then
            let varState =
                state.Substitution
                |> Map.toSeq
                |> Seq.map (fun (v, t) -> $"{v}: {t}")
                |> String.concat ","
            printfn $"Evaluating: {goal} ({varState})"

        match goal with
        | Goal.Equiv (t1, t2) ->
            match unify t1 t2 state with
            | None -> Stream.empty
            | Some unification -> Stream.Nonempty (unification, Stream.empty)
        | Goal.Fresh goal ->
            let newVar = state.VariableCounter

            Stream.Procedure (fun () ->
                evaluate'
                    debug
                    (goal newVar)
                    { state with
                        VariableCounter = Variable.incr state.VariableCounter
                    }
            )
        | Goal.Disj (goal1, goal2) ->
            Stream.union (evaluate' debug goal1 state) (evaluate' debug goal2 state)
        | Goal.Conj (goal1, goal2) -> Stream.bind (evaluate' debug goal1 state) (evaluate' debug goal2)
        | Goal.Delay g -> Stream.Procedure (fun () -> evaluate' debug (g ()) state)

    let evaluate (goal : Goal) = evaluate' false goal State.empty
