namespace FicroKanSharp

open System
open FSharp.Quotations
open FSharp.Quotations.Patterns

[<RequireQualifiedAccess>]
module internal Reflection =

    let invokeStaticMethod (e : Expr) : Type seq -> obj seq -> obj =
        let rec getMethodInfo =
            function
            | Call (_, mi, _) -> mi
            | Lambda (_, e) -> getMethodInfo e
            | _ -> failwith "Could not get MethodInfo"

        let mi =
            (getMethodInfo e).GetGenericMethodDefinition ()

        fun ts vs ->
            mi.MakeGenericMethod (ts |> Array.ofSeq)
            |> fun mi -> mi.Invoke (null, vs |> Array.ofSeq)
