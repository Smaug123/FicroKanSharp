namespace FicroKanSharp

[<RequireQualifiedAccess>]
module Term =

    let ofLiteral<'a> (a : 'a) : Term<'a> =
        Term.Symbol
