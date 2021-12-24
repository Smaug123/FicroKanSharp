namespace FicroKanSharp.Test

open FicroKanSharp
open FsUnitTyped
open Xunit

module Arithmetic =

    type Nat = Nat

    [<Fact>]
    let ``Arithmetic example`` () =
        let zero : Term<Nat> = Term.Symbol ("zero", [])

        let succ (x : Term<Nat>) : Term<Nat> =
            Term.Symbol ("succ", [ TypedTerm.make x ])

        let rec ofInt (n : int) : Term<Nat> =
            if n = 0 then
                zero
            else
                succ (ofInt (n - 1))

        // "pluso x y z" is "x + y == z".
        let rec pluso (x : Term<Nat>) (y : Term<Nat>) (z : Term<Nat>) : Goal =
            let succCase =
                Goal.callFresh (fun n ->
                    let n = Term.Variable n

                    Goal.callFresh (fun m ->
                        let m = Term.Variable m

                        Goal.conj
                            (Goal.equiv x (succ n))
                            (Goal.conj (Goal.equiv z (succ m)) (Goal.delay (fun () -> pluso n y m)))
                    )
                )

            let zeroCase =
                Goal.conj (Goal.equiv x zero) (Goal.equiv y z)

            Goal.disj zeroCase succCase

        Goal.evaluate (Goal.callFresh (fun z -> Goal.equiv<Nat> (Term.Variable z) (Term.Variable z))) State.empty
        |> Stream.toList
        |> shouldEqual [ Map.empty ]

        // Evaluate 1 + 1
        Goal.evaluate (Goal.callFresh (fun z -> pluso (ofInt 1) (ofInt 1) (Term.Variable z))) State.empty
        |> Stream.toList
        |> List.exactlyOne
        |> shouldEqual (
            Map.ofList
                [
                    VariableCount 0, TypedTerm.make (succ (Term.Variable (VariableCount 2)))
                    VariableCount 1, TypedTerm.make (ofInt 0)
                    VariableCount 2, TypedTerm.make (ofInt 1)
                ]
        )

        // Evaluate 2 + 2
        Goal.evaluate (Goal.callFresh (fun z -> pluso (ofInt 2) (ofInt 2) (Term.Variable z))) State.empty
        |> Stream.toList
        |> List.exactlyOne
        |> shouldEqual (
            Map.ofList
                [
                    VariableCount 0, TypedTerm.make (succ (Term.Variable (VariableCount 2)))
                    VariableCount 1, TypedTerm.make (ofInt 1)
                    VariableCount 2, TypedTerm.make (succ (Term.Variable (VariableCount 4)))
                    VariableCount 3, TypedTerm.make zero
                    VariableCount 4, TypedTerm.make (ofInt 2)
                ]
        )

        // Find n such that n + n = 4
        Goal.evaluate (Goal.callFresh (fun z -> pluso (Term.Variable z) (Term.Variable z) (ofInt 4))) State.empty
        |> Stream.toList
        |> List.exactlyOne
        |> shouldEqual (
            Map.ofList
                [
                    VariableCount 0, TypedTerm.make (succ (Term.Variable (VariableCount 1)))
                    VariableCount 1, TypedTerm.make (succ (Term.Variable (VariableCount 3)))
                    VariableCount 2, TypedTerm.make (ofInt 3)
                    VariableCount 3, TypedTerm.make zero
                    VariableCount 4, TypedTerm.make (ofInt 2)
                ]
        )
