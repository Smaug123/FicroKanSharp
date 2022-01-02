namespace FicroKanSharp

open System
open System.Collections.Generic
open System.Reflection
open FicroKanSharp
open FSharp.Reflection

type TypedTerm<'a> =
    | Term of Term
    | Literal of 'a

type private FSharpUnionCase =
    {
        Name : string
        Fields : PropertyInfo[]
        Constructor : obj[] -> obj
    }

[<NoComparison ; CustomEquality>]
type internal TypeName<'a when 'a : equality> =
    private
        {
            UserType : Type
            FieldValue : 'a
            UnionCases : (FSharpUnionCase array * (obj -> int)) option
        }

    override this.Equals (other : obj) : bool =
        match other with
        | :? TypeName<'a> as other ->
            this.UserType = other.UserType && this.FieldValue = other.FieldValue
        | _ -> false

    override this.GetHashCode () =
        hash (this.UserType, this.FieldValue)

    member private t1.Decompile (args : Term list) : obj =
        match t1.UnionCases with
        | None ->
            t1.FieldValue :> obj
        | Some (cases, tagDiscriminator) ->

        if t1.FieldValue.GetType () = typeof<string> then
            let case =
                cases
                |> Array.find (fun case -> case.Name = unbox<string> t1.FieldValue)

            args
            |> List.mapi (fun i term ->
                let expectedType = case.Fields.[i].PropertyType

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

                    let unboxed = mi.Invoke (name, [||]) |> unbox<TypeName<obj>>
                    let result = unboxed.Decompile args

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
            )
            |> Array.ofList
            |> case.Constructor
        else
            t1.FieldValue :> obj

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
                BindingFlags.Static
                ||| BindingFlags.Public
                ||| BindingFlags.FlattenHierarchy
                ||| BindingFlags.NonPublic
            )

        if obj.ReferenceEquals (unifyMethod, null) then
            None
        else

        if unifyMethod.ReturnParameter.ParameterType
           <> typeof<State option> then
            failwith
                $"Incorrect unify return parameter should have been Option<State>: {unifyMethod.ReturnParameter.ParameterType}"

        match unifyMethod.GetParameters () with
        | [| unifyParam ; _t1Param ; _t2Param ; stateParam |] ->
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

        let t1 = t1.Decompile args1
        let t2 = t2.Decompile args2

        let result =
            unifyMethod.Invoke (typeof<'a>, [| unify ; t1 ; t2 ; state |])
            |> unbox<State option>

        result

    member this.Unbox<'b when 'b : equality> () =
        {
            UserType = this.UserType
            FieldValue = unbox<'b> this.FieldValue
            UnionCases = this.UnionCases
        }

    override this.ToString () =
        $"{this.FieldValue}<%s{this.UserType.Name}>"

[<RequireQualifiedAccess>]
module TypedTerm =

    let variable<'a> (t : Variable) : TypedTerm<'a> = TypedTerm.Term (Term.Variable t)

    let literal<'a> (t : 'a) : TypedTerm<'a> = TypedTerm.Literal t

    let resolveGeneric (t : Type) : Type =
        if t.IsGenericType then
            t.GetGenericTypeDefinition ()
        else
            t

    let rec private toUntypedLiteral' (ty : Type) : obj -> Term =
        if ty = typeof<Variable> then
            fun t -> Term.Variable (unbox t)
        elif FSharpType.IsUnion ty then
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

            let resolved = resolveGeneric ty

            let precomputed = FSharpValue.PreComputeUnionTagReader ty
            let cases =
                FSharpType.GetUnionCases ty
                |> Array.map (fun case ->
                    {
                        Name = case.Name
                        Constructor = FSharpValue.PreComputeUnionConstructor case
                        Fields = case.GetFields ()
                    }
                )

            fun t ->
                let case = cases.[precomputed t]
                let values =
                    case.Fields
                    |> Array.map (fun pi -> pi.GetValue t)
                    |> toTermList

                Term.Symbol (
                    {
                        UserType = resolved
                        FieldValue = case.Name
                        UnionCases = Some (cases, precomputed)
                    },
                    values
                )
        else
            let resolved = resolveGeneric ty
            fun t ->
                Term.Symbol (
                    {
                        UserType = resolved
                        FieldValue = t
                        UnionCases = None
                    },
                    []
                )

    and private cache = Dictionary<Type, obj -> Term> ()

    and private toUntypedLiteral (o : obj) : Term =
        let ty = o.GetType ()
        match cache.TryGetValue ty with
        | false, _ ->
            let ans = toUntypedLiteral' (o.GetType ())
            cache.Add (ty, ans)
            ans o
        | true, f ->
            f o

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
