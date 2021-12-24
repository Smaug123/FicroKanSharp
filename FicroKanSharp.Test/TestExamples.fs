namespace FicroKanSharp.Test

open FicroKanSharp
open Xunit
open FsUnitTyped

module TestThing =

    [<Fact>]
    let ``Example from the docs`` () : unit =
        let aAndB =
            Goal.conj
                (Goal.callFresh (fun x -> Goal.equiv (Term.Variable x) (Term.Literal 7)))
                (Goal.callFresh (fun x ->
                    Goal.disj
                        (Goal.equiv (Term.Variable x) (Term.Literal 5))
                        (Goal.equiv (Term.Variable x) (Term.Literal 6))
                ))

        let u = Goal.evaluate aAndB State.empty

        match u |> Stream.peel with
        | None -> failwith "oh no"
        | Some (s, rest) ->

        s
        |> Map.map (fun _ -> TypedTerm.force<int>)
        |> Map.toList
        |> shouldEqual
            [
                Variable.VariableCount 0, Term.Literal 7
                Variable.VariableCount 1, Term.Literal 5
            ]

        match rest |> Stream.peel with
        | None -> failwith "oh no"
        | Some (s, rest) ->

        s
        |> Map.map (fun _ -> TypedTerm.force<int>)
        |> Map.toList
        |> shouldEqual
            [
                Variable.VariableCount 0, Term.Literal 7
                Variable.VariableCount 1, Term.Literal 6
            ]

        match rest |> Stream.peel with
        | None -> ()
        | Some s -> failwith $"{s}"

    [<Fact>]
    let ``Another example`` () =
        let aAndB =
            (Goal.callFresh (fun x -> Goal.equiv (Term.Variable x) (Term.Literal 5)))

        let u = Goal.evaluate aAndB State.empty

        match u |> Stream.peel with
        | None -> failwith "oh no"
        | Some (s, rest) ->

        s
        |> Map.map (fun _ -> TypedTerm.force<int>)
        |> Map.toList
        |> shouldEqual
            [
                Variable.VariableCount 0, Term.Literal 5
            ]

        match Stream.peel rest with
        | None -> ()
        | Some s -> failwithf $"{s}"

    [<Fact>]
    let ``Recursive example`` () =
        let rec fives (x : Variable) =
            (Goal.disj (Goal.equiv (Term.Variable x) (Term.Literal 5)) (Goal.delay (fun () -> fives x)))

        let u =
            Goal.evaluate (Goal.callFresh fives) State.empty

        match u |> Stream.peel with
        | None -> failwith "oh no"
        | Some (s, rest) ->

        s
        |> Map.map (fun _ -> TypedTerm.force<int>)
        |> Map.toList
        |> shouldEqual
            [
                Variable.VariableCount 0, Term.Literal 5
            ]

        match Stream.peel rest with
        | None -> failwith "oh no"
        | Some (s, rest) ->

        s
        |> Map.map (fun _ -> TypedTerm.force<int>)
        |> Map.toList
        |> shouldEqual
            [
                Variable.VariableCount 0, Term.Literal 5
            ]

        match Stream.peel rest with
        | None -> failwith "oh no"
        | Some (s, _rest) ->

            s
            |> Map.map (fun _ -> TypedTerm.force<int>)
            |> Map.toList
            |> shouldEqual
                [
                    Variable.VariableCount 0, Term.Literal 5
                ]

    [<Fact>]
    let ``Another recursive example`` () =
        let rec fives (x : Variable) =
            (Goal.disj (Goal.equiv (Term.Variable x) (Term.Literal 5)) (Goal.delay (fun () -> fives x)))

        let rec sixes (x : Variable) =
            (Goal.disj (Goal.equiv (Term.Variable x) (Term.Literal 6)) (Goal.delay (fun () -> sixes x)))

        let fivesAndSixes =
            Goal.callFresh (fun x -> Goal.disj (fives x) (sixes x))

        let u = Goal.evaluate fivesAndSixes State.empty

        match u |> Stream.peel with
        | None -> failwith "oh no"
        | Some (s, rest) ->

        s
        |> Map.map (fun _ -> TypedTerm.force<int>)
        |> Map.toList
        |> shouldEqual
            [
                Variable.VariableCount 0, Term.Literal 5
            ]

        match Stream.peel rest with
        | None -> failwith "oh no"
        | Some (s, rest) ->

        s
        |> Map.map (fun _ -> TypedTerm.force<int>)
        |> Map.toList
        |> shouldEqual
            [
                Variable.VariableCount 0, Term.Literal 6
            ]

        match Stream.peel rest with
        | None -> failwith "oh no"
        | Some (s, rest) ->

        s
        |> Map.map (fun _ -> TypedTerm.force<int>)
        |> Map.toList
        |> shouldEqual
            [
                Variable.VariableCount 0, Term.Literal 5
            ]

        match Stream.peel rest with
        | None -> failwith "oh no"
        | Some (s, _rest) ->

            s
            |> Map.map (fun _ -> TypedTerm.force<int>)
            |> Map.toList
            |> shouldEqual
                [
                    Variable.VariableCount 0, Term.Literal 6
                ]
