namespace FicroKanSharp.Test

open FicroKanSharp
open FsUnitTyped
open Xunit

module TestCustomUnification =

    [<RequireQualifiedAccess>]
    type Int =
        | Case1
        | Case2

    [<RequireQualifiedAccess>]
    type IntWithUnification =
        | Case1
        | Case2

        static member Unify
            (unify : Term -> Term -> bool option)
            (t1 : IntWithUnification)
            (args1 : Term list)
            (t2 : IntWithUnification)
            (args2 : Term list)
            : bool option
            =
            Some true

    [<Fact>]
    let ``Type with custom unification`` () =
        Goal.equiv (Term.Symbol (Int.Case1, [])) (Term.Symbol (Int.Case2, []))
        |> Goal.evaluate
        |> Reify.withRespectToFirst
        |> shouldBeEmpty

        Goal.equiv (Term.Symbol (Int.Case1, [])) (Term.Symbol (IntWithUnification.Case2, []))
        |> Goal.evaluate
        |> Reify.withRespectToFirst
        |> shouldBeEmpty

        Goal.equiv (Term.Symbol (IntWithUnification.Case1, [])) (Term.Symbol (Int.Case2, []))
        |> Goal.evaluate
        |> Reify.withRespectToFirst
        |> shouldBeEmpty

        Goal.equiv (Term.Symbol (IntWithUnification.Case1, [])) (Term.Symbol (IntWithUnification.Case2, []))
        |> Goal.evaluate
        |> Reify.withRespectToFirst
        |> Seq.exactlyOne
        |> Option.get
        |> shouldEqual (Term.Symbol (IntWithUnification.Case1, []))

    type Peano =
        | Pure of int
        | Zero
        | Succ

        static member Unify
            (unify : Term -> Term -> State -> State option)
            (t1 : Peano)
            (args1 : Term list)
            (t2 : Peano)
            (args2 : Term list)
            (state : State)
            : State option
            =
            match t1, t2 with
            | Zero, Zero
            | Succ, Succ
            | Pure _, Pure _ ->
                // Structural unification will do this
                None
            | Succ, Zero
            | Zero, Succ ->
                // These never unify
                None
            | Pure n, Zero
            | Zero, Pure n -> if n = 0 then Some state else None
            | Succ, Pure n ->
                if n = 0 then None else unify (List.exactlyOne args1) (Term.Symbol (Pure (n - 1), [])) state
            | Pure n, Succ ->
                if n = 0 then None else unify (Term.Symbol (Pure (n - 1), [])) (List.exactlyOne args2) state

    let rec toTerm (n : int) : Term =
        if n = 0 then Term.Symbol (Peano.Zero, []) else
        Term.Symbol (Peano.Succ, [toTerm (n - 1)])

    [<Fact>]
    let ``A custom augmented Peano naturals type`` () =
        Goal.equiv (Term.Symbol (Peano.Pure 5, [])) (toTerm 5)
        |> Goal.evaluate
        |> Reify.withRespectToFirst
        |> Seq.exactlyOne
        // Successful unification, no variables
        |> shouldEqual None

        Goal.equiv (toTerm 5) (Term.Symbol (Peano.Pure 5, []))
        |> Goal.evaluate
        |> Reify.withRespectToFirst
        |> Seq.exactlyOne
        // Successful unification, no variables
        |> shouldEqual None

        Goal.equiv (toTerm 4) (Term.Symbol (Peano.Pure 5, []))
        |> Goal.evaluate
        |> Reify.withRespectToFirst
        |> shouldBeEmpty

        Goal.callFresh (fun x -> Goal.equiv (Term.Symbol (Peano.Succ, [Term.Variable x])) (Term.Symbol (Peano.Pure 5, [])))
        |> Goal.evaluate
        |> Reify.withRespectToFirst
        |> Seq.exactlyOne
        |> Option.get
        |> shouldEqual (Term.Symbol (Peano.Pure 4, []))
