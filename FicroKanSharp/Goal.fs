namespace FicroKanSharp

[<RequireQualifiedAccess>]
[<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module Goal =
    let callFresh (f : Variable -> Goal) = Goal.Fresh f

    let delay g = Goal.Delay g

    /// Boolean "or": either goal must be satisfied.
    let disj (goal1 : Goal) (goal2 : Goal) : Goal = Goal.Disj (goal1, goal2)

    /// Boolean "and": both goals must be satisfied simultaneously.
    let conj (goal1 : Goal) (goal2 : Goal) : Goal = Goal.Conj (goal1, goal2)

    let equiv<'a when 'a : equality> (term1 : 'a Term) (term2 : 'a Term) : Goal =
        TermPairCrate.make term1 term2 |> Goal.Equiv

    let private walk<'a> (u : Term<'a>) (s : State) : Term<'a> =
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

    let private extend<'a when 'a : equality> (v : Variable) (t : Term<'a>) (s : State) =
        { s with
            Substitution = Map.add v (TermCrate.make t |> TypedTerm) s.Substitution
        }

    let rec private unify<'a when 'a : equality> (u : 'a Term) (v : 'a Term) (s : State) : State option =
        let u = walk u s
        let v = walk v s

        match u, v with
        | Term.Variable u, Term.Variable v when u = v -> s |> Some
        | Term.Variable u, v -> extend u v s |> Some
        | u, Term.Variable v -> extend v u s |> Some
        | Term.Literal u, Term.Literal v -> if u = v then Some s else None
        | Term.Symbol (name1, args1), Term.Symbol (name2, args2) ->
            if (name1 <> name2) || (args1.Length <> args2.Length) then
                None
            else

                let rec go state args1 args2 =
                    match args1, args2 with
                    | [], [] -> Some state
                    | _, []
                    | [], _ -> None
                    | TypedTerm arg1 :: args1, TypedTerm arg2 :: args2 ->
                        { new TermEvaluator<_> with
                            member _.Eval<'t when 't : equality> (arg1 : Term<'t>) =
                                { new TermEvaluator<_> with
                                    member _.Eval<'u when 'u : equality> (arg2 : Term<'u>) =
                                        if typeof<'t> = typeof<'u> then
                                            match unify arg1 (arg2 |> unbox) state with
                                            | None -> None
                                            | Some s -> go s args1 args2
                                        else
                                            None
                                }
                                |> arg2.Apply
                        }
                        |> arg1.Apply

                go s args1 args2

        | _, _ -> None

    let rec evaluate (goal : Goal) (state : State) : Stream =
        match goal with
        | Goal.Equiv pair ->
            { new TermPairEvaluator<_> with
                member _.Eval u v =
                    match unify u v state with
                    | None -> Stream.empty
                    | Some unification -> Stream.Nonempty (unification, Stream.empty)
            }
            |> pair.Apply
        | Goal.Fresh goal ->
            let newVar = state.VariableCounter

            evaluate
                (goal newVar)
                { state with
                    VariableCounter = Variable.incr state.VariableCounter
                }
        | Goal.Disj (goal1, goal2) -> Stream.union (evaluate goal1 state) (evaluate goal2 state)
        | Goal.Conj (goal1, goal2) -> Stream.bind (evaluate goal1 state) (evaluate goal2)
        | Goal.Delay g -> Stream.Procedure (fun () -> evaluate (g ()) state)

(*
    (dene (mK-reify s/c* )
(map reify-state/1st-var s/c* ))
(dene (reify-state/1st -var s/c)
(let ((v (walk* (var 0) (car s/c))))
(walk* v (reify-s v ' ()))))
The reier here, mK-reify, reies a list of states s/c*
by reifying each state's substitution with respect to the rst
variable. The reify-s, reify-name, and walk* helpers are
required for reify-state/1st-var.
(dene (reify-s v s)
(let ((v (walk v s)))
(cond
((var? v)
(let ((n (reify-name (length s))))
(cons `(, v . , n) s)))
((pair? v) (reify-s (cdr v) (reify-s (car v) s)))
(else s))))
(dene (reify-name n)
(stringsymbol
(string - append "_" "." (numberstring n))))
(dene (walk* v s)
(let ((v (walk v s)))
(cond
((var? v) v)
((pair? v) (cons (walk* (car v) s)
(walk* (cdr v) s)))
(else v))))
*)
