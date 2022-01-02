namespace FicroKanSharp.Test

open FicroKanSharp
open FsUnitTyped
open Xunit

module Arithmetic =

    [<Fact>]
    let ``Arithmetic example, untyped`` () =
        let zero : Term = Term.Symbol ("zero", [])

        let succ (x : Term) : Term = Term.Symbol ("succ", [ x ])

        let rec ofInt (n : int) : Term =
            if n = 0 then
                zero
            else
                succ (ofInt (n - 1))

        // "pluso x y z" is "x + y == z".
        let rec pluso (x : Term) (y : Term) (z : Term) : Goal =
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

        Goal.evaluate (Goal.callFresh (fun z -> Goal.equiv (Term.Variable z) (Term.Variable z)))
        |> Stream.toList
        |> shouldEqual [ Map.empty ]

        Goal.evaluate (pluso (ofInt 2) (ofInt 2) (ofInt 4))
        |> Stream.toList
        |> List.exactlyOne
        |> shouldEqual (
            Map.ofList
                [
                    VariableCount 0, ofInt 1
                    VariableCount 1, ofInt 3
                    VariableCount 2, zero
                    VariableCount 3, ofInt 2
                ]
        )

        // Evaluate 1 + 1
        Goal.evaluate (Goal.callFresh (fun z -> pluso (ofInt 1) (ofInt 1) (Term.Variable z)))
        |> Reify.withRespectToFirst
        |> Seq.exactlyOne
        |> Option.get
        |> shouldEqual (ofInt 2)

        // Evaluate 2 + 2
        Goal.evaluate (Goal.callFresh (fun z -> pluso (ofInt 2) (ofInt 2) (Term.Variable z)))
        |> Reify.withRespectToFirst
        |> Seq.exactlyOne
        |> Option.get
        |> shouldEqual (ofInt 4)

        // Find n such that n + n = 4
        Goal.evaluate (Goal.callFresh (fun z -> pluso (Term.Variable z) (Term.Variable z) (ofInt 4)))
        |> Reify.withRespectToFirst
        |> Seq.exactlyOne
        |> Option.get
        |> shouldEqual (ofInt 2)

    type Nat =
        | Zero
        | Succ of TypedTerm<Nat>

    [<Fact>]
    let ``Arithmetic example, typed`` () =
        let rec ofInt (n : int) : TypedTerm<Nat> =
            if n = 0 then
                Nat.Zero |> TypedTerm.literal
            else
                Nat.Succ (ofInt (n - 1)) |> TypedTerm.literal

        let succ (n : TypedTerm<Nat>) = Nat.Succ n |> TypedTerm.literal
        let zero = Nat.Zero |> TypedTerm.literal

        let rec numeralo (x : TypedTerm<Nat>) : Goal =
            Goal.disj
                (TypedTerm.Goal.equiv x (TypedTerm.literal Nat.Zero))
                (TypedTerm.Goal.callFresh (fun y ->
                    Goal.conj (Goal.delay (fun () -> numeralo y)) (TypedTerm.Goal.equiv x (succ y))
                ))

        // By the power of microKanren, let some numerals be manifested!

        Goal.evaluate (TypedTerm.Goal.callFresh numeralo)
        |> Reify.withRespectToFirst
        |> Seq.truncate 4
        |> Seq.toList
        |> List.map Option.get
        |> shouldEqual
            [
                TypedTerm.compile (ofInt 0)
                TypedTerm.compile (ofInt 1)
                TypedTerm.compile (ofInt 2)
                TypedTerm.compile (ofInt 3)
            ]

        // "pluso x y z" is "x + y == z".
        let rec pluso (x : TypedTerm<Nat>) (y : TypedTerm<Nat>) (z : TypedTerm<Nat>) : Goal =
            let z = z |> TypedTerm.compile

            let succCase =
                Goal.callFresh (fun n ->
                    let n = TypedTerm.variable n

                    Goal.callFresh (fun m ->
                        let m = TypedTerm.variable m

                        Goal.conj
                            (Goal.equiv (TypedTerm.compile x) (TypedTerm.compile (succ n)))
                            (Goal.conj (Goal.equiv z (succ m |> TypedTerm.compile)) (Goal.delay (fun () -> pluso n y m)))
                    )
                )

            let zeroCase =
                Goal.conj
                    (Goal.equiv (TypedTerm.compile x) (TypedTerm.compile zero))
                    (Goal.equiv (TypedTerm.compile y) z)

            Goal.disj zeroCase succCase

        Goal.evaluate (pluso (ofInt 2) (ofInt 2) (ofInt 4))
        |> Stream.toList
        |> List.exactlyOne
        |> shouldEqual (
            Map.ofList
                [
                    VariableCount 0, (ofInt 1 |> TypedTerm.compile)
                    VariableCount 1, (ofInt 3 |> TypedTerm.compile)
                    VariableCount 2, TypedTerm.compile zero
                    VariableCount 3, (ofInt 2 |> TypedTerm.compile)
                ]
        )

        // Evaluate 1 + 1
        Goal.evaluate (Goal.callFresh (fun z -> pluso (ofInt 1) (ofInt 1) (TypedTerm.variable z)))
        |> Reify.withRespectToFirst
        |> Seq.exactlyOne
        |> Option.get
        |> shouldEqual (TypedTerm.compile (ofInt 2))

        // Evaluate 2 + 2
        Goal.evaluate (Goal.callFresh (fun z -> pluso (ofInt 2) (ofInt 2) (TypedTerm.variable z)))
        |> Reify.withRespectToFirst
        |> Seq.exactlyOne
        |> Option.get
        |> shouldEqual (TypedTerm.compile (ofInt 4))

        // Find all n such that n + n = 4
        Goal.evaluate (Goal.callFresh (fun z -> pluso (TypedTerm.variable z) (TypedTerm.variable z) (ofInt 4)))
        |> Reify.withRespectToFirst
        |> Seq.exactlyOne
        |> Option.get
        |> shouldEqual (TypedTerm.compile (ofInt 2))
