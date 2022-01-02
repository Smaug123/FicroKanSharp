namespace FicroKanSharp

open Microsoft.FSharp.Core

type Variable = internal VariableCount of int

[<RequireQualifiedAccess>]
module private Variable =
    let incr (VariableCount v) = VariableCount (v + 1)

type Term =
    internal
    | Variable of Variable
    | Symbol of name : obj * args : Term list

    override this.ToString () =
        match this with
        | Symbol (name, args) ->
            let s =
                args
                |> List.map (sprintf "%O")
                |> String.concat ", "

            $"{name}[{s}]"
        | Variable (VariableCount v) -> $"x{v}"

type Goal =
    private
    | Equiv of Term * Term
    | Disj of Goal * Goal
    | Conj of Goal * Goal
    | Fresh of (Variable -> Goal)
    | Delay of (unit -> Goal)

    member private this.ToString (variableCount : int) : string =
        match this with
        | Fresh g ->
            if variableCount > 4 then "<exists x: ...>" else
            $"exists x{variableCount}: ({(g (VariableCount variableCount)).ToString (variableCount + 1)})"
        | Conj (g1, g2) -> sprintf "((%s) AND (%s))" (g1.ToString variableCount) (g2.ToString variableCount)
        | Disj (g1, g2) -> sprintf "((%s) OR  (%s))" (g1.ToString variableCount) (g2.ToString variableCount)
        | Equiv (g1, g2) -> sprintf "(%O) == (%O)" g1 g2
        | Delay g -> sprintf "delayed (%O)" (g().ToString (variableCount))

    override this.ToString () =
        this.ToString 0

/// This type is public so that the user can define their own Unify methods.
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
module private State =
    let empty =
        {
            VariableCounter = VariableCount 0
            Substitution = Map.empty
        }
