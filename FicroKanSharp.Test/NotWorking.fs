namespace FicroKanSharp.Test

open FicroKanSharp
open Xunit
open FsUnitTyped

module NotWorking =

    type LiteralNat =
        | LiteralNat of int
        | Succ of Term<LiteralNat>

    [<Fact>]
    let ``Arithmetic example using literals`` () =
        let zero : Term<LiteralNat> = Term.ofLiteral (LiteralNat 0)

        let succ (x : Term<LiteralNat>) : Term<LiteralNat> =
            Term.ofLiteral (LiteralNat.Succ x)

        let rec ofInt (n : int) : Term<LiteralNat> = LiteralNat n |> Term.ofLiteral

        let rec equal (x : Term<LiteralNat>) (y : Term<LiteralNat>) : Goal =
            match x, y with
            | Term.Literal (LiteralNat _) as x, (Term.Literal (LiteralNat _) as y) ->
                Goal.equiv x y
            | Term.Literal (LiteralNat x), Term.Literal (Succ t) ->
                if x = 0 then Goal.never else
                equal (Term.Literal (LiteralNat (x - 1))) t
            | Term.Literal (Succ x), Term.Literal (LiteralNat t) ->
                if t = 0 then Goal.never else
                equal x (Term.Literal (LiteralNat (t - 1)))
            | Term.Literal (Succ x), Term.Literal (Succ y) ->
                equal x y
            | Term.Symbol _, _
            | _, Term.Symbol _ ->
                failwith "hmmm"
            | x, (Term.Variable _ as y) -> Goal.equiv x y
            | Term.Variable _ as x, y -> Goal.equiv x y

        // "pluso x y z" is "x + y == z".
        let rec pluso (x : Term<LiteralNat>) (y : Term<LiteralNat>) (z : Term<LiteralNat>) : Goal =
            let succCase =
                Goal.callFresh (fun n ->
                    let n = Term.Variable n

                    Goal.callFresh (fun m ->
                        let m = Term.Variable m

                        Goal.conj
                            (equal x (succ n))
                            (Goal.conj (equal z (succ m)) (Goal.delay (fun () -> pluso n y m)))
                    )
                )

            let zeroCase =
                Goal.conj (equal x zero) (equal y z)

            Goal.disj zeroCase succCase

        Goal.callFresh (fun n ->
            let n = Term.Variable n // should be 1

            Goal.callFresh (fun m ->
                let m = Term.Variable m // should be 3

                let delayed =
                    Goal.callFresh (fun a ->
                        let a = Term.Variable a // should be 0

                        Goal.callFresh (fun b ->
                            let b = Term.Variable b // should be 2

                            Goal.conj
                                (equal n (succ a))
                                (Goal.conj (equal m (succ b)) (Goal.conj (equal a zero) (equal (ofInt 2) b)))
                        )
                    )

                Goal.conj
                    (equal (ofInt 2) (succ n))
                    (Goal.conj (equal (ofInt 4) (succ m)) delayed)
            )
        )
        |> Goal.evaluate
        //Goal.evaluate (pluso (ofInt 2) (ofInt 2) (ofInt 4))
        |> Stream.toList
        |> List.exactlyOne
        |> shouldEqual Map.empty

        Goal.evaluate (pluso (ofInt 2) (ofInt 2) (ofInt 5))
        |> Stream.toList
        |> printfn "%O"

        // Evaluate 1 + 1
        Goal.evaluate (Goal.callFresh (fun z -> pluso (ofInt 1) (ofInt 1) (Term.Variable z)))
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
        Goal.evaluate (Goal.callFresh (fun z -> pluso (ofInt 2) (ofInt 2) (Term.Variable z)))
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
        Goal.evaluate (Goal.callFresh (fun z -> pluso (Term.Variable z) (Term.Variable z) (ofInt 4)))
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

