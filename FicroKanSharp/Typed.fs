namespace FicroKanSharp

open System
open Microsoft.FSharp.Reflection

type TypedTerm<'a> =
    | Term of Term
    | Literal of 'a

type internal TypeName<'a> =
    {
        UserType : Type
        FieldValue : 'a
    }
    override this.ToString () =
        sprintf "%O<%s>" this.FieldValue this.UserType.Name

[<RequireQualifiedAccess>]
module TypedTerm =

    let variable<'a> (t : Variable) : TypedTerm<'a> = TypedTerm.Term (Term.Variable t)

    let literal<'a> (t : 'a) : TypedTerm<'a> = TypedTerm.Literal t

    let rec private toUntypedLiteral<'a when 'a : equality> (t : 'a) : Term =
        let ty = typeof<'a>

        if ty = typeof<Variable> then
            Term.Variable (unbox t)
        elif FSharpType.IsUnion ty then
            let fieldU, valuesU =
                FSharpValue.GetUnionFields (t, typeof<'a>)

            let toTermList (o : obj []) : Term list =
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

            Term.Symbol ({ UserType = td ; FieldValue = fieldU.Name }, valuesU)
        else
            Term.Symbol ({ UserType = ty ; FieldValue = t }, [])

    and private ofLiteral : Type -> obj -> Term =
        let m =
            Reflection.invokeStaticMethod <@ toUntypedLiteral @>

        fun tl o -> m [ tl ] [ o ] |> unbox

    and private compileUntyped : Type -> obj -> Term =
        let m =
            Reflection.invokeStaticMethod <@ compile @>

        fun tl o -> m [ tl ] [ o ] |> unbox

    and compile<'a when 'a : equality> (t : TypedTerm<'a>) : Term =
        match t with
        | TypedTerm.Term t -> t
        | TypedTerm.Literal u -> toUntypedLiteral u

    [<RequireQualifiedAccess>]
    module Goal =
        let callFresh<'a> (f : TypedTerm<'a> -> Goal) : Goal =
            Goal.callFresh (fun v -> f (variable<'a> v))

        let equiv (t1 : TypedTerm<'a>) (t2 : TypedTerm<'a>) : Goal = Goal.equiv (compile t1) (compile t2)
