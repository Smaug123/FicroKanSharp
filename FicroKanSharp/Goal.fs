namespace FicroKanSharp

open FicroKanSharp

[<RequireQualifiedAccess>]
[<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module Goal =
    let callFresh (f : Variable -> Goal) = Goal.Fresh f

    let delay g = Goal.Delay g

    /// Boolean "or": either goal must be satisfied.
    let disj (goal1 : Goal) (goal2 : Goal) : Goal = Goal.Disj (goal1, goal2)

    /// Boolean "and": both goals must be satisfied simultaneously.
    let conj (goal1 : Goal) (goal2 : Goal) : Goal = Goal.Conj (goal1, goal2)

    let equiv (term1 : UntypedTerm) (term2 : UntypedTerm) : Goal =
        Goal.Equiv (term1, term2)

    let equiv'<'a, 'b when 'a : equality and 'b : equality> (term1 : 'a Term) (term2 : 'b Term) : Goal =
        equiv (UntypedTerm.make term1) (UntypedTerm.make term2)

    let never : Goal =
        equiv (Term.Symbol ("_internal", []) |> UntypedTerm.make) (Term.Symbol ("_internal", [ Term.Symbol ("_internal", []) |> UntypedTerm.make ]) |> UntypedTerm.make)

    let always : Goal =
        equiv (Term.Symbol ("_internal", []) |> UntypedTerm.make) (Term.Symbol ("_internal", []) |> UntypedTerm.make)

    let private walk<'a when 'a : equality> (u : Term<'a>) (s : State) : UntypedTerm =
        match u with
        | Term.Variable u as x ->
            match Map.tryFind u s.Substitution with
            | None -> x |> UntypedTerm.make
            | Some subst ->
                subst
        | u -> u |> UntypedTerm.make

    let private extend<'a when 'a : equality> (v : Variable) (t : Term<'a>) (s : State) =
        { s with
            Substitution = Map.add v (TermCrate.make t |> UntypedTerm) s.Substitution
        }

    let rec private unifyList (args1 : _) (args2 : _) (state : State) : State option =
        match args1, args2 with
        | [], [] -> Some state
        | _, []
        | [], _ -> None
        | UntypedTerm arg1 :: args1, UntypedTerm arg2 :: args2 ->
            { new TermEvaluator<_> with
                member _.Eval<'t when 't : equality> (arg1 : Term<'t>) =
                    { new TermEvaluator<_> with
                        member _.Eval<'u when 'u : equality> (arg2 : Term<'u>) =
                            match unify arg1 arg2 state with
                            | None -> None
                            | Some state -> unifyList args1 args2 state
                    }
                    |> arg2.Apply
            }
            |> arg1.Apply

    and private unify<'a, 'b when 'a : equality and 'b : equality> (u : 'a Term) (v : 'b Term) (s : State) : State option =
        let (UntypedTerm u) = walk u s
        let (UntypedTerm v) = walk v s

        { new TermEvaluator<_> with
            member _.Eval u =
                { new TermEvaluator<_> with
                    member _.Eval v =
                        match u, v with
                        | Term.Variable u, Term.Variable v when u = v -> s |> Some
                        | Term.Variable u, v -> extend u v s |> Some
                        | u, Term.Variable v -> extend v u s |> Some
                        | Term.Symbol (name1, args1), Term.Symbol (name2, args2) ->
                            if name1.GetType () <> name2.GetType () then None else
                            let name2 = unbox name2
                            if (name1 <> name2) || (args1.Length <> args2.Length) then
                                None
                            else
                                unifyList args1 args2 s

                        | _, _ -> None
                }
                |> v.Apply
        }
        |> u.Apply

    let rec private evaluate' (goal : Goal) (state : State) : Stream =
        match goal with
        | Goal.Equiv (UntypedTerm t1, UntypedTerm t2) ->
            { new TermEvaluator<_> with
                member _.Eval u =
                    { new TermEvaluator<_> with
                        member _.Eval v =
                            match unify u v state with
                            | None -> Stream.empty
                            | Some unification -> Stream.Nonempty (unification, Stream.empty)
                    }
                    |> t2.Apply
            }
            |> t1.Apply
        | Goal.Fresh goal ->
            let newVar = state.VariableCounter

            evaluate'
                (goal newVar)
                { state with
                    VariableCounter = Variable.incr state.VariableCounter
                }
        | Goal.Disj (goal1, goal2) -> Stream.union (evaluate' goal1 state) (evaluate' goal2 state)
        | Goal.Conj (goal1, goal2) -> Stream.bind (evaluate' goal1 state) (evaluate' goal2)
        | Goal.Delay g -> Stream.Procedure (fun () -> evaluate' (g ()) state)

    let evaluate (goal : Goal) = evaluate' goal State.empty

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
