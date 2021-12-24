namespace FicroKanSharp

[<RequireQualifiedAccess>]
[<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module Goal =
    let callFresh (f : Variable -> Goal) = Goal.Fresh f

    let delay g = Goal.Delay g

    let disj (goal1 : Goal) (goal2 : Goal) : Goal = Goal.Disj (goal1, goal2)

    let conj (goal1 : Goal) (goal2 : Goal) : Goal = Goal.Conj (goal1, goal2)

    let equiv<'a when 'a : equality> (term1 : 'a Term) (term2 : 'a Term) : Goal =
        TermPairCrate.make term1 term2 |> Goal.Equiv

    let walk<'a> (u : Term<'a>) (s : State) : Term<'a> =
        match u with
        | Term.Variable u ->
            match Map.tryFind u s.Substitution with
            | None -> Term.Variable u
            | Some (TypedTerm subst) ->
                { new TermEvaluator<_> with
                    member _.Eval x = unbox x
                }
                |> subst.Apply
        | u -> u

    let extend<'a> (v : Variable) (t : Term<'a>) (s : State) =
        { s with
            Substitution = Map.add v (TermCrate.make t |> TypedTerm) s.Substitution
        }

    let rec unify<'a when 'a : equality> (u : 'a Term) (v : 'a Term) (s : State) : State option =
        let u = walk u s
        let v = walk v s

        match u, v with
        | Term.Variable u, Term.Variable v when u = v -> s |> Some
        | Term.Variable u, v -> extend u v s |> Some
        | u, Term.Variable v -> extend v u s |> Some
        | Term.Literal u, Term.Literal v -> if u = v then Some s else None

    let rec evaluate (goal : Goal) (state : State) : Stream =
        match goal with
        | Goal.Equiv pair ->
            { new TermPairEvaluator<_> with
                member _.Eval u v =
                    match unify u v state with
                    | None -> Stream.mzero
                    | Some unification -> Stream.Nonempty (unification, Stream.mzero)
            }
            |> pair.Apply
        | Goal.Fresh goal ->
            let newVar = state.VariableCounter

            evaluate
                (goal newVar)
                { state with
                    VariableCounter = Variable.incr state.VariableCounter
                }
        | Goal.Disj (goal1, goal2) -> Stream.mplus (evaluate goal1 state) (evaluate goal2 state)
        | Goal.Conj (goal1, goal2) -> Stream.bind (evaluate goal1 state) (evaluate goal2)
        | Goal.Delay g -> Stream.Procedure (fun () -> evaluate (g ()) state)
