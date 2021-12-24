namespace FicroKanSharp

type Variable = internal VariableCount of int

[<RequireQualifiedAccess>]
module private Variable =
    let incr (VariableCount v) = VariableCount (v + 1)

type Term<'a> =
    | Literal of 'a
    | Variable of Variable
    | Symbol of name : string * args : TypedTerm list

    override this.ToString () =
        match this with
        | Symbol (name, args) ->
            let s =
                args
                |> List.map (sprintf "%O")
                |> String.concat ", "

            $"{name}[{s}]"
        | Variable (VariableCount v) -> $"x{v}"
        | Literal t -> t.ToString ()

and internal TermEvaluator<'ret> =
    abstract Eval<'a when 'a : equality> : 'a Term -> 'ret

and internal TermCrate =
    abstract Apply<'ret> : TermEvaluator<'ret> -> 'ret

and [<CustomEquality ; NoComparison>] TypedTerm =
    internal
    | TypedTerm of TermCrate

    override this.Equals (other : obj) : bool =
        match this with
        | TypedTerm tc ->

        match other with
        | :? TypedTerm as other ->
            match other with
            | TypedTerm other -> tc.Equals other
        | _ -> false

    override this.GetHashCode () =
        match this with
        | TypedTerm tc ->
            { new TermEvaluator<_> with
                override _.Eval t = t.GetHashCode ()
            }
            |> tc.Apply

    override this.ToString () =
        match this with
        | TypedTerm tc -> tc.ToString ()

[<RequireQualifiedAccess>]
module internal TermCrate =
    let make<'a when 'a : equality> (t1 : 'a Term) =
        { new obj() with
            override this.ToString () = t1.ToString ()

            override this.Equals other =
                match other with
                | :? TermCrate as other ->
                    { new TermEvaluator<_> with
                        member _.Eval<'b when 'b : equality> (other : 'b Term) =
                            if typeof<'a> = typeof<'b> then
                                t1 = unbox other
                            else

                            printfn "%+A, %+A" typeof<'a> typeof<'b>
                            false
                    }
                    |> other.Apply
                | _ -> false
          interface TermCrate with
              member _.Apply eval = eval.Eval t1
        }

[<RequireQualifiedAccess>]
module TypedTerm =
    let force<'a> (TypedTerm t) : 'a Term =
        { new TermEvaluator<_> with
            member _.Eval t = unbox t
        }
        |> t.Apply

    let make<'a when 'a : equality> (t : 'a Term) : TypedTerm = TermCrate.make t |> TypedTerm

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
