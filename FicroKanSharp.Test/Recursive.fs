namespace FicroKanSharp.Test

open Xunit
open FsUnitTyped
open FicroKanSharp

module Recursive =

    type Entity =
        | Mosquito
        | Frog
        | Stork
        | Blood of TypedTerm<Entity>
        | Name of TypedTerm<string>

    [<Fact>]
    let ``Recursive definitions, example 1`` () : unit =
        let justAte (t1 : TypedTerm<Entity>) (t2 : TypedTerm<Entity>) : Goal =
            Goal.disj
                (Goal.conj
                    (TypedTerm.Goal.equiv t1 (TypedTerm.literal Entity.Mosquito))
                    (TypedTerm.Goal.equiv
                        t2
                        (TypedTerm.Literal (Entity.Blood (TypedTerm.literal (Entity.Name (TypedTerm.literal "john")))))))
                (Goal.disj
                    (Goal.conj
                        (TypedTerm.Goal.equiv t1 (TypedTerm.literal Entity.Frog))
                        (TypedTerm.Goal.equiv t2 (TypedTerm.literal Entity.Mosquito)))
                    (Goal.conj
                        (TypedTerm.Goal.equiv t1 (TypedTerm.literal Entity.Stork))
                        (TypedTerm.Goal.equiv t2 (TypedTerm.literal Entity.Frog))))

        let rec isDigesting (t1 : TypedTerm<Entity>) (t2 : TypedTerm<Entity>) : Goal =
            Goal.disj
                (justAte t1 t2)
                (TypedTerm.Goal.callFresh (fun z ->
                    Goal.delay (fun () -> Goal.conj (isDigesting t1 z) (isDigesting z t2))
                ))

        let stream =
            isDigesting (TypedTerm.literal Entity.Stork) (TypedTerm.literal Entity.Mosquito)
            |> Goal.evaluate

        let fst, _ = stream |> Stream.peel |> Option.get

        fst
        |> shouldEqual (
            Map.ofList
                [
                    // The stork is digesting the mosquito, via the frog which the stork just ate.
                    VariableCount 0, TypedTerm.Literal Entity.Frog |> TypedTerm.compile
                ]
        )

    // There is no second element of the stream, but FicroKanSharp will search
    // forever without realising this.
    // It will forever try to find z such that `isDigesting Stork z` and `isDigesting z Mosquito`.

    type Human = Human of string

    [<Fact>]
    let ``Recursive definitions, example 2`` () : unit =
        let children =
            [
                "anne", "bridget"
                "bridget", "caroline"
                "caroline", "donna"
                "donna", "emily"
            ]
            |> List.map (fun (parent, child) -> TypedTerm.literal (Human parent), TypedTerm.literal (Human child))

        let child (t1 : TypedTerm<Human>) (t2 : TypedTerm<Human>) : Goal =
            children
            |> List.fold
                (fun state (parent, child) ->
                    Goal.conj (TypedTerm.Goal.equiv parent t1) (TypedTerm.Goal.equiv t2 child)
                    |> Goal.disj state
                )
                Goal.never

        let rec descend (t1 : TypedTerm<Human>) (t2 : TypedTerm<Human>) : Goal =
            Goal.disj
                (child t1 t2)
                (TypedTerm.Goal.callFresh (fun z -> Goal.conj (child t1 z) (Goal.delay (fun () -> descend z t2))))

        child (TypedTerm.literal (Human "anne")) (TypedTerm.literal (Human "donna"))
        |> Goal.evaluate
        |> Stream.toList
        |> shouldBeEmpty

        child (TypedTerm.literal (Human "anne")) (TypedTerm.literal (Human "bridget"))
        |> Goal.evaluate
        |> Stream.toList
        |> List.exactlyOne
        |> shouldEqual (Map.ofList [])

        descend (TypedTerm.literal (Human "anne")) (TypedTerm.literal (Human "donna"))
        |> Goal.evaluate
        |> Stream.toList
        |> List.exactlyOne
        |> shouldEqual (
            Map.ofList
                [
                    VariableCount 0, TypedTerm.literal (Human "bridget") |> TypedTerm.compile
                    VariableCount 1, TypedTerm.literal (Human "caroline") |> TypedTerm.compile
                ]
        )
