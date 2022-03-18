let rec maxsub xs =
    match xs with
    | [] -> None
    | [ x ] -> Some x
    | _ ->
        let rec go ys acc mx =
            match ys with
            | [] -> mx
            | y :: ys ->
                if y + acc > mx then
                    go ys (y + acc) (y + acc)
                else
                    mx

        let (lhs, rhs) = List.splitAt (xs.Length / 2) xs
        let l = go (List.rev lhs) 0 0
        let r = go rhs 0 0
        let lm = Option.toList (maxsub lhs)
        let rm = Option.toList (maxsub rhs)

        Some(List.max ([ l + r ] @ lm @ rm))
