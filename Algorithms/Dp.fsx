let rec fib0 n =
    match n with
    | 1 -> 1
    | 2 -> 2
    | n -> fib0 (n - 1) + fib0 (n - 2)

let fib1 n =
    let mutable arr = Array.create (n + 1) 0
    arr.[1] <- 1
    arr.[2] <- 2

    if n > 2 then
        [ 3 .. n ]
        |> List.iter (fun i -> arr.[i] <- arr.[i - 1] + arr.[i - 2])
    else
        ()

    arr.[n]
