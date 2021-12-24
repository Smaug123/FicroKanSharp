namespace FicroKanSharp

type Variable = internal VariableCount of int

[<RequireQualifiedAccess>]
module private Variable =
    let incr (VariableCount v) = VariableCount (v + 1)

type Term =
    | Literal of int
    | Variable of Variable

type Goal =
    private
    | Equiv of Term * Term
    | Disj of Goal * Goal
    | Conj of Goal * Goal
    | Fresh of (Variable -> Goal)
    | Delay of (unit -> Goal)

type State =
    internal
        {
            Substitution : Map<Variable, Term>
            VariableCounter : Variable
        }

type Stream =
    private
    | Empty
    | Procedure of (unit -> Stream)
    | Nonempty of State * Stream

[<RequireQualifiedAccess>]
module State =
    let empty =
        {
            VariableCounter = VariableCount 0
            Substitution = Map.empty
        }

[<RequireQualifiedAccess>]
module Stream =
    let mzero : Stream = Stream.Empty

    let rec mplus (s1 : Stream) (s2 : Stream) : Stream =
        match s1 with
        | Stream.Empty -> s2
        | Stream.Procedure s -> Stream.Procedure (fun () -> mplus s2 (s ()))
        | Stream.Nonempty (fst, rest) -> Stream.Nonempty (fst, mplus rest s2)

    let rec bind (s : Stream) (g : State -> Stream) =
        match s with
        | Stream.Empty -> mzero
        | Stream.Procedure s -> Stream.Procedure (fun () -> bind (s ()) g)
        | Stream.Nonempty (fst, rest) -> mplus (g fst) (bind rest g)

    let rec peel (s : Stream) : (Map<Variable, Term> * Stream) option =
        match s with
        | Stream.Empty -> None
        | Stream.Nonempty (fst, rest) -> Some (fst.Substitution, rest)
        | Stream.Procedure p -> peel (p ())

[<RequireQualifiedAccess>]
module Goal =
    let callFresh (f : Variable -> Goal) = Goal.Fresh f

    let delay g = Goal.Delay g

    let disj (goal1 : Goal) (goal2 : Goal) : Goal = Goal.Disj (goal1, goal2)

    let conj (goal1 : Goal) (goal2 : Goal) : Goal = Goal.Conj (goal1, goal2)

    let equiv (term1 : Term) (term2 : Term) : Goal = Goal.Equiv (term1, term2)

    let walk (u : Term) (s : State) : Term =
        match u with
        | Term.Variable u ->
            match Map.tryFind u s.Substitution with
            | None -> Term.Variable u
            | Some subst -> subst
        | u -> u

    let extend (v : Variable) (t : Term) (s : State) =
        { s with
            Substitution = Map.add v t s.Substitution
        }

    let rec unify u v (s : State) : State option =
        let u = walk u s
        let v = walk v s

        match u, v with
        | Term.Variable u, Term.Variable v when u = v -> s |> Some
        | Term.Variable u, v -> extend u v s |> Some
        | u, Term.Variable v -> extend v u s |> Some
        | Term.Literal u, Term.Literal v -> if u = v then Some s else None

    let rec evaluate (goal : Goal) (state : State) : Stream =
        match goal with
        | Goal.Equiv (u, v) ->
            // (let ((s (unify u v (car s/c))))
//(if s (unit `(, s . , (cdr s/c))) mzero))))
            match unify u v state with
            | None -> Stream.mzero
            | Some unification -> Stream.Nonempty (unification, Stream.mzero)
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
