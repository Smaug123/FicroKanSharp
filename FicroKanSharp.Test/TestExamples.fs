namespace FicroKanSharp.Test

open FicroKanSharp
open Xunit
open FsUnitTyped

module TestThing =

    [<Fact>]
    let ``Example from the docs`` () : unit =
        let aAndB =
            Goal.conj
                (Goal.callFresh (fun x -> Goal.equiv (Term.Variable x) (Term.Symbol (7, []))))
                (Goal.callFresh (fun x ->
                    Goal.disj
                        (Goal.equiv (Term.Variable x) (Term.Symbol (5, [])))
                        (Goal.equiv (Term.Variable x) (Term.Symbol (6, [])))
                ))

        let u = Goal.evaluate aAndB

        match u |> Stream.peel with
        | None -> failwith "oh no"
        | Some (s, rest) ->

        s
        |> Map.toList
        |> shouldEqual
            [
                Variable.VariableCount 0, Term.Symbol (7, [])
                Variable.VariableCount 1, Term.Symbol (5, [])
            ]

        match rest |> Stream.peel with
        | None -> failwith "oh no"
        | Some (s, rest) ->

        s
        |> Map.toList
        |> shouldEqual
            [
                Variable.VariableCount 0, Term.Symbol (7, [])
                Variable.VariableCount 1, Term.Symbol (6, [])
            ]

        match rest |> Stream.peel with
        | None -> ()
        | Some s -> failwith $"{s}"

    [<Fact>]
    let ``Another example`` () =
        let aAndB =
            (Goal.callFresh (fun x -> Goal.equiv (Term.Variable x) (Term.Symbol (5, []))))

        let u = Goal.evaluate aAndB

        match u |> Stream.peel with
        | None -> failwith "oh no"
        | Some (s, rest) ->

        s
        |> Map.toList
        |> shouldEqual
            [
                Variable.VariableCount 0, Term.Symbol (5, [])
            ]

        match Stream.peel rest with
        | None -> ()
        | Some s -> failwithf $"{s}"

    [<Fact>]
    let ``Recursive example`` () =
        let rec fives (x : Variable) =
            (Goal.disj (Goal.equiv (Term.Variable x) (Term.Symbol (5, []))) (Goal.delay (fun () -> fives x)))

        Goal.evaluate (Goal.callFresh fives)
        |> Stream.take 3
        |> shouldEqual
            [
                Map.ofList
                    [
                        Variable.VariableCount 0, Term.Symbol (5, [])
                    ]
                Map.ofList
                    [
                        Variable.VariableCount 0, Term.Symbol (5, [])
                    ]
                Map.ofList
                    [
                        Variable.VariableCount 0, Term.Symbol (5, [])
                    ]
            ]

    [<Fact>]
    let ``Another recursive example`` () =
        let rec fives (x : Variable) =
            (Goal.disj (Goal.equiv (Term.Variable x) (Term.Symbol (5, []))) (Goal.delay (fun () -> fives x)))

        let rec sixes (x : Variable) =
            (Goal.disj (Goal.equiv (Term.Variable x) (Term.Symbol (6, []))) (Goal.delay (fun () -> sixes x)))

        let fivesAndSixes =
            Goal.callFresh (fun x -> Goal.disj (fives x) (sixes x))

        let u = Goal.evaluate fivesAndSixes

        match u |> Stream.peel with
        | None -> failwith "oh no"
        | Some (s, rest) ->

        s
        |> Map.toList
        |> shouldEqual
            [
                Variable.VariableCount 0, Term.Symbol (5, [])
            ]

        match Stream.peel rest with
        | None -> failwith "oh no"
        | Some (s, rest) ->

        s
        |> Map.toList
        |> shouldEqual
            [
                Variable.VariableCount 0, Term.Symbol (6, [])
            ]

        match Stream.peel rest with
        | None -> failwith "oh no"
        | Some (s, rest) ->

        s
        |> Map.toList
        |> shouldEqual
            [
                Variable.VariableCount 0, Term.Symbol (5, [])
            ]

        match Stream.peel rest with
        | None -> failwith "oh no"
        | Some (s, _rest) ->

            s
            |> Map.toList
            |> shouldEqual
                [
                    Variable.VariableCount 0, Term.Symbol (6, [])
                ]

    /// This arose because x0 unified to x1, x1 unified to 1, but x0 didn't get reduced to 1 by `walk`.
    [<Fact>]
    let ``Unification works transitively`` () =
        Goal.callFresh (fun twon -> // 0

            let succCase =
                Goal.callFresh (fun n ->
                    Goal.conj
                        (Goal.equiv (Term.Variable twon) (Term.Variable n))
                        (Goal.equiv (Term.Symbol ("something", [])) (Term.Variable twon))
                )

            Goal.conj succCase (Goal.equiv (Term.Variable twon) (Term.Symbol ("another", [])))
        )
        |> Goal.evaluate
        |> Reify.withRespectToFirst
        |> shouldBeEmpty
