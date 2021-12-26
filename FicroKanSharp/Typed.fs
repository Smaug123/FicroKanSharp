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

    let literal<'a> (t : 'a) : TypedTerm<'a> = TypedTerm.Literal t

    let private untypedTerm : Type -> obj -> UntypedTerm =
        let m =
            Reflection.invokeStaticMethod <@ UntypedTerm.make @>

        fun tl o -> m [ tl ] [ o ] |> unbox

    let rec private toUntypedLiteral<'a when 'a : equality> (t : 'a) : UntypedTerm =
        let ty = typeof<'a>

        if ty = typeof<Variable> then
            UntypedTerm.make<unit> (Term.Variable (unbox t))
        elif FSharpType.IsUnion ty then
            let fieldU, valuesU =
                FSharpValue.GetUnionFields (t, typeof<'a>)

            let toTermList (o : obj []) : UntypedTerm list =
                o
                |> List.ofArray
                |> List.map (fun (o : obj) ->
                    let ty = o.GetType ()

                    if ty.BaseType.IsGenericType
                       && ty.BaseType.GetGenericTypeDefinition () = typedefof<TypedTerm<obj>>.GetGenericTypeDefinition
                           () then
                        o |> compileUntyped ty.GenericTypeArguments.[0]
                    else
                        ofLiteral ty o
                )

            let valuesU = toTermList valuesU
            let td = typedefof<'a>

            Term.Symbol ((td, fieldU.Name), valuesU)
            |> UntypedTerm.make
        else
            UntypedTerm.make (Term.Symbol ((ty, t), []))

    and private ofLiteral : Type -> obj -> UntypedTerm =
        let m =
            Reflection.invokeStaticMethod <@ toUntypedLiteral @>

        fun tl o -> m [ tl ] [ o ] |> unbox

    and private compileUntyped : Type -> obj -> UntypedTerm =
        let m =
            Reflection.invokeStaticMethod <@ compile @>

        fun tl o -> m [ tl ] [ o ] |> unbox

    and compile<'a when 'a : equality> (t : TypedTerm<'a>) : UntypedTerm =
        match t with
        | TypedTerm.Term t -> t
        | TypedTerm.Literal u -> toUntypedLiteral u

    [<RequireQualifiedAccess>]
    module Goal =
        let callFresh<'a> (f : TypedTerm<'a> -> Goal) : Goal =
            Goal.callFresh (fun v -> f (variable<'a> v))

        let equiv (t1 : TypedTerm<'a>) (t2 : TypedTerm<'a>) : Goal = Goal.equiv (compile t1) (compile t2)
