namespace FicroKanSharp

[<RequireQualifiedAccess>]
[<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module Stream =
    /// This is called mzero in the microKanren paper.
    let internal empty : Stream = Stream.Empty

    /// This is called mplus in the microKanren paper.
    let rec internal union (s1 : Stream) (s2 : Stream) : Stream =
        match s1 with
        | Stream.Empty -> s2
        | Stream.Procedure s -> Stream.Procedure (fun () -> union s2 (s ()))
        | Stream.Nonempty (fst, rest) -> Stream.Nonempty (fst, union rest s2)

    let rec internal bind (s : Stream) (g : State -> Stream) : Stream =
        match s with
        | Stream.Empty -> empty
        | Stream.Procedure s -> Stream.Procedure (fun () -> bind (s ()) g)
        | Stream.Nonempty (fst, rest) -> union (g fst) (bind rest g)

    let rec peel (s : Stream) : (Map<Variable, UntypedTerm> * Stream) option =
        match s with
        | Stream.Empty -> None
        | Stream.Nonempty (fst, rest) -> Some (fst.Substitution, rest)
        | Stream.Procedure p -> peel (p ())

    /// This will stack-overflow for an infinite stream.
    let toList (s : Stream) : Map<Variable, UntypedTerm> list =
        let rec go acc s =
            match s with
            | Stream.Empty -> acc
            | Stream.Nonempty (fst, rest) -> go (fst.Substitution :: acc) rest
            | Stream.Procedure p -> go acc (p ())

        go [] s |> List.rev
