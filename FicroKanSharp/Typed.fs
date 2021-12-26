namespace FicroKanSharp

type TypedTerm<'a> =
    | Term of Term<'a>
    | Literal of 'a

[<RequireQualifiedAccess>]
module Typed =

    let compile<'a> (t : TypedTerm<'a>) : Term<'a> =
        match t with
        | Term t -> t
        | Literal l ->