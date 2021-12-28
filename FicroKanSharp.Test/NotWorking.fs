namespace FicroKanSharp.Test

open FicroKanSharp
open Xunit
open FsUnitTyped

module NotWorking =

    type Int =
        | Pure of int
        | Succ of TypedTerm<Int>

        static member Unify (unify : Term -> Term -> State option) (t1 : Int) (t2 : Int) : State option =
            match t1, t2 with
            | Pure _, Pure _
            | Succ _, Succ _ ->
                // Ordinary structural unification will handle this
                None
            | Succ t1, Pure t2 ->
                if t2 = 0 then
                    Some false
                else
                    unify t1 (Pure (t2 - 1) |> TypedTerm.literal)
            | Pure t1, Succ t2 ->
                if t1 = 0 then
                    Some false
                else
                    unify (Pure (t1 - 1) |> TypedTerm.literal) t2

    [<Fact>]
    let ``Arithmetic example using literals`` () =
        let zero = TypedTerm.literal (Int.Pure 0)

        let succ (x : TypedTerm<Int>) : TypedTerm<Int> =
            match x with
            // Little efficiency saving
            | TypedTerm.Literal (Int.Pure x) -> TypedTerm.Literal (x + 1 |> Int.Pure)
            | _ -> TypedTerm.Literal (Int.Succ x)

        let rec ofInt (n : int) : TypedTerm<Int> = Int.Pure n |> TypedTerm.Literal

        let rec equal (x : Int) (y : Int) : Goal =
            match x, y with
            | Int.Pure x, Int.Pure y ->
                if x = y then
                    Goal.always
                else
                    Goal.never
            | Int.Succ x, Int.Succ y -> equal x y
            | TypedTerm.Literal (Int.Pure x), TypedTerm.Literal (Int.Succ y) ->
                Goal.delay (fun () -> equal (TypedTerm.Literal (Int.Pure (x - 1))) y)
            | TypedTerm.Literal (Int.Succ x), TypedTerm.Literal (Int.Pure y) ->
                Goal.delay (fun () -> equal x (TypedTerm.Literal (Int.Pure (y - 1))))

        // "pluso x y z" is "x + y == z".
        let rec pluso (x : TypedTerm<Int>) (y : TypedTerm<Int>) (z : TypedTerm<Int>) : Goal =
            let succCase =
                TypedTerm.Goal.callFresh (fun n ->
                    TypedTerm.Goal.callFresh (fun m ->
                        Goal.conj (equal x (succ n)) (Goal.conj (equal z (succ m)) (Goal.delay (fun () -> pluso n y m)))
                    )
                )

            let zeroCase = Goal.conj (equal x zero) (equal y z)

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
                                (equal n (succ a))
                                (Goal.conj (equal m (succ b)) (Goal.conj (equal a zero) (equal (ofInt 2) b)))
                        )
                    )

                Goal.conj (equal (ofInt 2) (succ n)) (Goal.conj (equal (ofInt 4) (succ m)) delayed)
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
        Goal.evaluate (Goal.callFresh (fun z -> pluso (ofInt 1) (ofInt 1) (TypedTerm.variable z)))
        |> Stream.toList
        |> List.exactlyOne
        |> shouldEqual (
            Map.ofList
                [
                    VariableCount 0, TypedTerm.compile (succ (TypedTerm.variable (VariableCount 2)))
                    VariableCount 1, TypedTerm.compile (ofInt 0)
                    VariableCount 2, TypedTerm.compile (ofInt 1)
                ]
        )

        // Evaluate 2 + 2
        Goal.evaluate (Goal.callFresh (fun z -> pluso (ofInt 2) (ofInt 2) (TypedTerm.variable z)))
        |> Stream.toList
        |> List.exactlyOne
        |> shouldEqual (
            Map.ofList
                [
                    VariableCount 0, TypedTerm.compile (succ (TypedTerm.variable (VariableCount 2)))
                    VariableCount 1, TypedTerm.compile (ofInt 1)
                    VariableCount 2, TypedTerm.compile (succ (TypedTerm.variable (VariableCount 4)))
                    VariableCount 3, TypedTerm.compile zero
                    VariableCount 4, TypedTerm.compile (ofInt 2)
                ]
        )

        // Find n such that n + n = 4
        Goal.evaluate (Goal.callFresh (fun z -> pluso (TypedTerm.variable z) (TypedTerm.variable z) (ofInt 4)))
        |> Stream.toList
        |> List.exactlyOne
        |> shouldEqual (
            Map.ofList
                [
                    VariableCount 0, TypedTerm.compile (succ (TypedTerm.variable (VariableCount 1)))
                    VariableCount 1, TypedTerm.compile (succ (TypedTerm.variable (VariableCount 3)))
                    VariableCount 2, TypedTerm.compile (ofInt 3)
                    VariableCount 3, TypedTerm.compile zero
                    VariableCount 4, TypedTerm.compile (ofInt 2)
                ]
        )
