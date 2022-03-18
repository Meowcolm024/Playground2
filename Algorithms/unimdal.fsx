let rec unimodal xs =
    match xs with
    | [] -> None
    | x :: [] -> Some x
    | x :: y :: [] -> Some(if x < y then x else y)
    | _ ->
        let mid = xs.Length / 2
        let (l, r) = List.splitAt mid xs
        if xs.[mid - 1] > xs.[mid] 
            then unimodal r
            else unimodal l
