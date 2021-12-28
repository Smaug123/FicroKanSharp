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

    static member Unify
        (_unify : Term -> Term -> State -> State option)
        (_t1 : TypeName<'a>)
        (_args1 : Term list)
        (_t2 : TypeName<'a>)
        (_args2 : Term list)
        (state : State)
        : State option
        =
        failwith "implement"

[<RequireQualifiedAccess>]
module TypedTerm =

    let variable<'a> (t : Variable) : TypedTerm<'a> = TypedTerm.Term (Term.Variable t)

    let literal<'a> (t : 'a) : TypedTerm<'a> = TypedTerm.Literal t

    let resolveGeneric (t : Type) : Type =
        if t.IsGenericType then
            t.GetGenericTypeDefinition ()
        else
            t

    let rec private toUntypedLiteral (t : obj) : Term =
        let ty = t.GetType ()

        if ty = typeof<Variable> then
            Term.Variable (unbox t)
        elif FSharpType.IsUnion ty then
            let fieldU, valuesU = FSharpValue.GetUnionFields (t, ty)

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
                        toUntypedLiteral o
                )

            let valuesU = toTermList valuesU

            Term.Symbol (
                {
                    UserType = resolveGeneric ty
                    FieldValue = fieldU.Name
                },
                valuesU
            )
        else
            Term.Symbol (
                {
                    UserType = resolveGeneric ty
                    FieldValue = t
                },
                []
            )

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
