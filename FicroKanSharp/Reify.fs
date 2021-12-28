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

    let rec reify (state : Map<Variable, Term>) (term : Term) : Term =
        match term with
        | Term.Variable v -> Map.find v state |> reify state
        | Term.Symbol (name, args) ->

        let args = args |> List.map (reify state)

        Term.Symbol (name, args)

    let rec withRespectToFirst (s : Stream) : seq<Term option> =
        seq {
            match Stream.peel s with
            | None -> ()
            | Some (first, other) ->
                match Map.toSeq first |> Seq.tryHead with
                | None -> yield None
                | Some (variable, _) -> yield Some (reify first (Term.Variable variable))

                yield! withRespectToFirst other
        }
