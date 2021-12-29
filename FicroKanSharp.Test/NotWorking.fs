namespace FicroKanSharp.Test

open FicroKanSharp
open Xunit
open FsUnitTyped

module NotWorking =

    type Int =
        | Pure of int
        | Succ of TypedTerm<Int>

        static member Unify
            (unify : Term -> Term -> State -> State option)
            (t1 : Int)
            (t2 : Int)
            (state : State)
            : State option
            =
            match t1, t2 with
            | Pure _, Pure _
            | Succ _, Succ _ ->
                // Ordinary structural unification will handle this
                None
            | Succ t1, Pure t2 ->
                if t2 = 0 then
                    None
                else
                    unify
                        (TypedTerm.compile t1)
                        (Pure (t2 - 1)
                         |> TypedTerm.literal
                         |> TypedTerm.compile)
                        state
            | Pure t1, Succ t2 ->
                if t1 = 0 then
                    None
                else
                    unify (TypedTerm.compile (Pure (t1 - 1) |> TypedTerm.literal)) (TypedTerm.compile t2) state

    [<Fact>]
    let ``Arithmetic example using literals`` () =
        let zero = TypedTerm.literal (Int.Pure 0)

        let succ (x : TypedTerm<Int>) : TypedTerm<Int> =
            match x with
            // Little efficiency saving
            | TypedTerm.Literal (Int.Pure x) -> TypedTerm.Literal (x + 1 |> Int.Pure)
            | _ -> TypedTerm.Literal (Int.Succ x)

        let rec ofInt (n : int) : TypedTerm<Int> = Int.Pure n |> TypedTerm.Literal

        // "pluso x y z" is "x + y == z".
        let rec pluso (x : TypedTerm<Int>) (y : TypedTerm<Int>) (z : TypedTerm<Int>) : Goal =
            let succCase =
                TypedTerm.Goal.callFresh (fun n ->
                    TypedTerm.Goal.callFresh (fun m ->
                        Goal.conj
                            (TypedTerm.Goal.equiv x (succ n))
                            (Goal.conj (TypedTerm.Goal.equiv z (succ m)) (Goal.delay (fun () -> pluso n y m)))
                    )
                )

            let zeroCase =
                Goal.conj (TypedTerm.Goal.equiv x zero) (TypedTerm.Goal.equiv y z)

            Goal.disj zeroCase succCase

        Goal.callFresh (fun n ->
            let n = TypedTerm.variable n // should be 1

            Goal.callFresh (fun m ->
                let m = TypedTerm.variable m // should be 3

                let delayed =
                    Goal.callFresh (fun a ->
                        let a = TypedTerm.variable a // should be 0

                        Goal.callFresh (fun b ->
                            let b = TypedTerm.variable b // should be 2

                            Goal.conj
                                (TypedTerm.Goal.equiv n (succ a))
                                (Goal.conj
                                    (TypedTerm.Goal.equiv m (succ b))
                                    (Goal.conj (TypedTerm.Goal.equiv a zero) (TypedTerm.Goal.equiv (ofInt 2) b)))
                        )
                    )

                Goal.conj
                    (TypedTerm.Goal.equiv (ofInt 2) (succ n))
                    (Goal.conj (TypedTerm.Goal.equiv (ofInt 4) (succ m)) delayed)
            )
        )
        |> Goal.evaluate
        |> Stream.toList
        |> List.exactlyOne
        |> shouldEqual (
            Map.ofList
                [
                    VariableCount 0, Pure 1 |> TypedTerm.literal |> TypedTerm.compile
                    VariableCount 1, Pure 3 |> TypedTerm.literal |> TypedTerm.compile
                    VariableCount 2, Pure 0 |> TypedTerm.literal |> TypedTerm.compile
                    VariableCount 3, Pure 2 |> TypedTerm.literal |> TypedTerm.compile
                ]
        )

        // Evaluate 1 + 1
        let onePlusOne =
            Goal.evaluate (Goal.callFresh (fun z -> pluso (ofInt 1) (ofInt 1) (TypedTerm.variable z)))
            |> Reify.withRespectToFirst
            |> Seq.exactlyOne
            |> Option.get

        Goal.evaluate (Goal.equiv onePlusOne (TypedTerm.literal (Pure 2) |> TypedTerm.compile))
        |> Reify.withRespectToFirst
        |> Seq.exactlyOne
        |> shouldEqual None

        // Evaluate 2 + 2
        let twoPlusTwo =
            Goal.evaluate (Goal.callFresh (fun z -> pluso (ofInt 2) (ofInt 2) (TypedTerm.variable z)))
            |> Reify.withRespectToFirst
            |> Seq.exactlyOne
            |> Option.get

        Goal.evaluate (Goal.equiv twoPlusTwo (TypedTerm.literal (Pure 4) |> TypedTerm.compile))
        |> Reify.withRespectToFirst
        |> Seq.exactlyOne
        |> shouldEqual None

        // Find n such that n + n = 4
        let halfFour =
            Goal.evaluate (Goal.callFresh (fun z -> pluso (TypedTerm.variable z) (TypedTerm.variable z) (ofInt 4)))
            |> Reify.withRespectToFirst
            |> Seq.exactlyOne
            |> Option.get

        Goal.evaluate (Goal.equiv halfFour (TypedTerm.literal (Pure 2) |> TypedTerm.compile))
        |> Reify.withRespectToFirst
        |> Seq.exactlyOne
        |> shouldEqual None
