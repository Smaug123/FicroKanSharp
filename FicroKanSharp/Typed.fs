namespace FicroKanSharp

open System
open System.Reflection
open FicroKanSharp
open Microsoft.FSharp.Reflection

type TypedTerm<'a> =
    | Term of Term
    | Literal of 'a

[<CustomEquality ; NoComparison>]
type internal TypeName<'a when 'a : equality> =
    {
        UserType : Type
        FieldValue : 'a
        OriginalValue : obj
    }

    member this.Unbox<'b when 'b : equality> () =
        {
            UserType = this.UserType
            FieldValue = unbox<'b> this.FieldValue
            OriginalValue = this.OriginalValue
        }

    override this.Equals (other : obj) : bool =
        match other with
        | :? TypeName<'a> as other ->
            this.UserType = other.UserType
            && this.FieldValue = other.FieldValue
        | _ -> false

    override this.GetHashCode () : int = hash (this.UserType, this.FieldValue)

    override this.ToString () =
        sprintf "%O<%s>" this.FieldValue this.UserType.Name

    static member Unify
        (unify : Term -> Term -> State -> State option)
        (t1 : TypeName<'a>)
        (args1 : Term list)
        (t2 : TypeName<'a>)
        (args2 : Term list)
        (state : State)
        : State option
        =
        let unifyMethod =
            t1.UserType.GetMethod (
                "Unify",
                System.Reflection.BindingFlags.Static
                ||| System.Reflection.BindingFlags.Public
                ||| System.Reflection.BindingFlags.FlattenHierarchy
                ||| System.Reflection.BindingFlags.NonPublic
            )

        if obj.ReferenceEquals (unifyMethod, null) then
            None
        else

        if unifyMethod.ReturnParameter.ParameterType
           <> typeof<State option> then
            failwith
                $"Incorrect unify return parameter should have been Option<State>: {unifyMethod.ReturnParameter.ParameterType}"

        match unifyMethod.GetParameters () with
        | [| unifyParam ; t1Param ; t2Param ; stateParam |] ->
            let wrongParams =
                [
                    let t =
                        typeof<Term -> Term -> State -> State option>

                    if unifyParam.ParameterType <> t then
                        yield nameof unifyParam, t

                    let t = typeof<State>

                    if stateParam.ParameterType <> t then
                        yield nameof stateParam, t
                ]

            match wrongParams with
            | [] -> ()
            | wrongParams ->
                let wrongParams =
                    wrongParams
                    |> List.map (fun (s, ty) -> $"{s} (expected: {ty.Name})")
                    |> String.concat "; "

                failwith $"Wrong parameters on Unify method of type {t1.UserType.Name}: {wrongParams}"
        | parameters ->
            failwith $"Wrong parameter count on Unify method of type {t1.UserType.Name}: {Array.toList parameters}"

        let rec decompile (t1 : TypeName<obj>) (args : Term list) : obj =
            if FSharpType.IsUnion t1.UserType
               && t1.FieldValue.GetType () = typeof<string> then
                let unionCases = FSharpType.GetUnionCases t1.UserType

                let case =
                    unionCases
                    |> Array.find (fun case -> case.Name = unbox<string> t1.FieldValue)

                let fields = case.GetFields ()

                args
                |> List.mapi (fun i term ->
                    let expectedType = fields.[i].PropertyType

                    match term with
                    | Term.Symbol (name, args) ->
                        let mi =
                            name
                                .GetType()
                                .GetMethod(
                                    "Unbox",
                                    BindingFlags.Public
                                    ||| BindingFlags.NonPublic
                                    ||| BindingFlags.Instance
                                )
                                .MakeGenericMethod typeof<obj>

                        let unboxed = mi.Invoke (name, [||])
                        let result = decompile (unbox unboxed) args

                        if expectedType.IsGenericType
                           && expectedType.GetGenericTypeDefinition () = typedefof<TypedTerm<obj>> then
                            let unionCase =
                                FSharpType.GetUnionCases expectedType
                                |> Array.find (fun uc -> uc.Name = "Literal")

                            FSharpValue.MakeUnion (unionCase, [| result |])
                        else
                            result
                    | Term.Variable _ as var ->
                        let typedTermUci =
                            typedefof<TypedTerm<obj>>.MakeGenericType expectedType.GenericTypeArguments
                            |> FSharpType.GetUnionCases
                            |> Array.find (fun uci -> uci.Name = "Term")

                        FSharpValue.MakeUnion (typedTermUci, [| unbox var |])
                //Reflection.invokeStaticMethod <@ unbox @> [| t |] [| var |]
                )
                |> Array.ofList
                |> fun i ->
                    i
                    |> Array.map (sprintf "%O")
                    |> String.concat ","
                    |> printfn "Making union case %O with arg %s" case.Name

                    FSharpValue.MakeUnion (case, i)
            else
                t1.FieldValue

        let t1 = decompile (t1.Unbox<obj> ()) args1
        let t2 = decompile (t2.Unbox<obj> ()) args2

        (*
        let t2 =
            if t2.GetType () = typeof<TypeName<string>> then
                let t2 = unbox<TypeName<string>> t2
                let case = unionCases |> Array.find (fun case -> case.Name = t2.FieldValue)
                FSharpValue.MakeUnion (case, args2 |> List.map (failwith "") |> Array.ofList)
            else failwith $"oh no 2: {t2.GetType ()}"
            *)

        let result =
            unifyMethod.Invoke (typeof<'a>, [| unify ; t1 ; t2 ; state |])
            |> unbox<State option>

        result

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
                    OriginalValue = t
                },
                valuesU
            )
        else
            Term.Symbol (
                {
                    UserType = resolveGeneric ty
                    FieldValue = t
                    OriginalValue = t
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
