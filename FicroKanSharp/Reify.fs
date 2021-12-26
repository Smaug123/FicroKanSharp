namespace FicroKanSharp

[<RequireQualifiedAccess>]
module Reify =

    let private collectList<'a> (l : 'a option list) : 'a list option =
        let rec go (acc : 'a list) (xs : 'a option list) =
            match xs with
            | [] -> Some (List.rev acc)
            | None :: _ -> None
            | Some x :: rest -> go (x :: acc) rest

        go [] l

    let rec reify (state : Map<Variable, Term>) (term : Term) : Term option =
        match term with
        | Term.Variable v -> Map.tryFind v state |> Option.bind (reify state)
        | Term.Symbol (name, args) ->

        let args =
            args |> List.map (reify state) |> collectList

        match args with
        | None -> None
        | Some args ->

        Term.Symbol (name, args) |> Some

    let rec withRespectToFirst (s : Stream) : seq<Term option> =
        seq {
            match Stream.peel s with
            | None -> ()
            | Some (first, other) ->
                yield
                    reify
                        first
                        (first
                         |> Map.toSeq
                         |> Seq.head
                         |> fst
                         |> Term.Variable)

                yield! withRespectToFirst other
        }
