namespace FicroKanSharp

[<RequireQualifiedAccess>]
[<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module Stream =
    let mzero : Stream = Stream.Empty

    let rec mplus (s1 : Stream) (s2 : Stream) : Stream =
        match s1 with
        | Stream.Empty -> s2
        | Stream.Procedure s -> Stream.Procedure (fun () -> mplus s2 (s ()))
        | Stream.Nonempty (fst, rest) -> Stream.Nonempty (fst, mplus rest s2)

    let rec bind (s : Stream) (g : State -> Stream) =
        match s with
        | Stream.Empty -> mzero
        | Stream.Procedure s -> Stream.Procedure (fun () -> bind (s ()) g)
        | Stream.Nonempty (fst, rest) -> mplus (g fst) (bind rest g)

    let rec peel (s : Stream) : (Map<Variable, TypedTerm> * Stream) option =
        match s with
        | Stream.Empty -> None
        | Stream.Nonempty (fst, rest) -> Some (fst.Substitution, rest)
        | Stream.Procedure p -> peel (p ())
