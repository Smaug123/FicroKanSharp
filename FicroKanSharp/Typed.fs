namespace FicroKanSharp

open System
open Microsoft.FSharp.Reflection

type TypedTerm<'a> =
    | Term of UntypedTerm
    | Literal of 'a

[<RequireQualifiedAccess>]
module TypedTerm =

    let variable<'a> (t : Variable) : TypedTerm<'a> =
        TypedTerm.Term (UntypedTerm.make (Term.Variable t : Term<unit>))

    let private toUntypedLiteral<'a when 'a : equality> (t : 'a) : UntypedTerm =
        Term.Symbol ((typeof<'a>, t), [])
        |> UntypedTerm.make

    let private untypedTerm : Type -> obj -> UntypedTerm =
        let m = Reflection.invokeStaticMethod <@ UntypedTerm.make @>
        fun tl o -> m [tl] [o] |> unbox
    let private ofLiteral : Type -> obj -> UntypedTerm =
        let m = Reflection.invokeStaticMethod <@ toUntypedLiteral @>
        fun tl o -> m [tl] [o] |> unbox

    let rec compileUntyped : Type -> obj -> UntypedTerm =
        let m = Reflection.invokeStaticMethod <@ compile @>
        fun tl o -> m [tl] [o] |> unbox

    and compile<'a when 'a : equality> (t : TypedTerm<'a>) : UntypedTerm =
        match t with
        | TypedTerm.Term t -> t
        | TypedTerm.Literal u ->
            if FSharpType.IsUnion typeof<'a> then
                let fieldU, valuesU = FSharpValue.GetUnionFields (u, typeof<'a>)
                let toTermList (o : obj []) : UntypedTerm list =
                    o
                    |> List.ofArray
                    |> List.map (fun (o : obj) ->
                        let ty = o.GetType ()
                        if ty.IsGenericType && ty.BaseType.GetGenericTypeDefinition () = typedefof<TypedTerm<obj>>.GetGenericTypeDefinition () then
                            o
                            |> compileUntyped ty.GenericTypeArguments.[0]
                        else
                            ofLiteral ty o
                    )
                let valuesU = toTermList valuesU
                Term.Symbol ((typeof<'a>, fieldU.Name), valuesU)
                |> UntypedTerm.make
            else
                failwith $"Unsupported type: {typeof<'a>}"