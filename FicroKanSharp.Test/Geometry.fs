namespace FicroKanSharp.Test

// Taken from http://www.let.rug.nl/bos/lpn//lpnpage.php?pagetype=html&pageid=lpn-htmlse5

open FsUnitTyped
open FicroKanSharp
open Xunit

module Geometry =

    type Point<'a> =
        | Point of TypedTerm<'a> * TypedTerm<'a>

    type Line<'a> =
        | Line of TypedTerm<Point<'a>> * TypedTerm<Point<'a>>

    let verticalo<'a when 'a : equality> (line : TypedTerm<Line<'a>>) : Goal =
        fun x ->
             fun y ->
                 fun z ->
                     Line (TypedTerm<Point<'a>>.Literal (Point (x, y)), TypedTerm.Literal (Point (x, z)))
                     |> TypedTerm.Literal
                     |> TypedTerm.Goal.equiv line
                 |> TypedTerm.Goal.callFresh
            |> TypedTerm.Goal.callFresh
        |> TypedTerm.Goal.callFresh

    let horizontalo<'a when 'a : equality> (line : TypedTerm<Line<'a>>) : Goal =
        fun x ->
             fun y ->
                 fun z ->
                     Line (TypedTerm<Point<'a>>.Literal (Point (x, y)), TypedTerm.Literal (Point (z, y)))
                     |> TypedTerm.Literal
                     |> TypedTerm.Goal.equiv line
                 |> TypedTerm.Goal.callFresh
            |> TypedTerm.Goal.callFresh
        |> TypedTerm.Goal.callFresh

    [<Fact>]
    let ``Geometry example from Learn Prolog Now`` () =
        Line (TypedTerm.Literal (Point (TypedTerm.Literal 1, TypedTerm.Literal 1)), TypedTerm.Literal (Point (TypedTerm.Literal 1, TypedTerm.Literal 3)))
        |> TypedTerm.Literal
        |> verticalo
        |> Goal.evaluate
        |> Stream.toList
        |> List.exactlyOne
        |> shouldEqual (Map.ofList [
            VariableCount 0, TypedTerm.compile (TypedTerm.Literal 1)
            VariableCount 1, TypedTerm.compile (TypedTerm.Literal 1)
            VariableCount 2, TypedTerm.compile (TypedTerm.Literal 3)
        ])

        (Line (TypedTerm.Literal (Point (TypedTerm.Literal 1, TypedTerm.Literal 1)), TypedTerm.Literal (Point (TypedTerm.Literal 3, TypedTerm.Literal 2))))
        |> TypedTerm.Literal
        |> verticalo
        |> Goal.evaluate
        |> Stream.toList
        |> shouldEqual []

        Goal.callFresh (fun y ->
            Line (TypedTerm.Literal (Point (TypedTerm.Literal 1, TypedTerm.Literal 1)), TypedTerm.Literal (Point (TypedTerm.Literal 2, TypedTerm.variable y)))
            |> TypedTerm.Literal
            |> horizontalo
        )
        |> Goal.evaluate
        |> Stream.toList
        |> List.exactlyOne
        |> shouldEqual (Map.ofList [
            // There is y such that (1,1) = (2, y), and it is 1.
            VariableCount 0, TypedTerm.compile (TypedTerm.Literal 1)
            // There is x,y,z such that (x,y) = (z,y) where (x,y) = (1,1) and (z,y) = (2, y)
            // and they are 1, 1, and 2.
            VariableCount 1, TypedTerm.compile (TypedTerm.Literal 1)
            VariableCount 2, TypedTerm.compile (TypedTerm.Literal 1)
            VariableCount 3, TypedTerm.compile (TypedTerm.Literal 2)
        ])

        Goal.callFresh (fun y ->
            Line (TypedTerm.Literal (Point (TypedTerm.Literal 2, TypedTerm.Literal 3)), TypedTerm.variable y)
            |> TypedTerm.Literal
            |> horizontalo
        )
        |> Goal.evaluate
        |> Stream.toList
        |> List.exactlyOne
        |> shouldEqual (Map.ofList [
            // There is a point p such that (2,3) -> p is horizontal.
            // It is (x3, x2).
            VariableCount 0, TypedTerm.compile (TypedTerm.Literal (Point (TypedTerm.variable (VariableCount 3), TypedTerm.variable (VariableCount 2))))
            // This is the x-coordinate, which doesn't reify in the final answer.
            VariableCount 1, TypedTerm.compile (TypedTerm.Literal 2)
            // x2 is 3.
            VariableCount 2, TypedTerm.compile (TypedTerm.Literal 3)
            // Notice that x3 is not constrained.
        ])
