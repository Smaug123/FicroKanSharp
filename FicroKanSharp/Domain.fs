namespace FicroKanSharp

type Variable = internal VariableCount of int

[<RequireQualifiedAccess>]
module private Variable =
    let incr (VariableCount v) = VariableCount (v + 1)

type Term<'a> =
    | Literal of 'a
    | Variable of Variable

/// Equality constraint is required because we use this crate for unification
type internal TermPairEvaluator<'ret> =
    abstract Eval<'a when 'a : equality> : 'a Term -> 'a Term -> 'ret

type internal TermPairCrate =
    abstract Apply<'ret> : TermPairEvaluator<'ret> -> 'ret

[<RequireQualifiedAccess>]
module internal TermPairCrate =
    let make<'a when 'a : equality> (t1 : 'a Term) (t2 : 'a Term) =
        { new TermPairCrate with
            member _.Apply eval = eval.Eval t1 t2
        }

type internal TermEvaluator<'ret> =
    abstract Eval<'a> : 'a Term -> 'ret

type internal TermCrate =
    abstract Apply<'ret> : TermEvaluator<'ret> -> 'ret

[<RequireQualifiedAccess>]
module internal TermCrate =
    let make<'a> (t1 : 'a Term) =
        { new TermCrate with
            member _.Apply eval = eval.Eval t1
        }

type TypedTerm = internal TypedTerm of TermCrate

[<RequireQualifiedAccess>]
module TypedTerm =
    let force<'a> (TypedTerm t) : 'a Term =
        { new TermEvaluator<_> with
            member _.Eval t = unbox t
        }
        |> t.Apply

type Goal =
    private
    | Equiv of TermPairCrate
    | Disj of Goal * Goal
    | Conj of Goal * Goal
    | Fresh of (Variable -> Goal)
    | Delay of (unit -> Goal)

type State =
    internal
        {
            Substitution : Map<Variable, TypedTerm>
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
