
type term =
    | TmVar of int * int
    | TmAbs of string * term
    | TmApp of term * term

let termShift d t =
    let rec walk c t =
        match t with
        | TmVar (x, n) ->
            if x >= c then
                TmVar(x + d, c + d)
            else
                TmVar(x, n + d)
        | TmAbs (x, t1) -> TmAbs(x, walk (c + 1) t1)
        | TmApp (t1, t2) -> TmApp(walk c t1, walk c t2)

    walk 0 t

let termSubst j s t =
    let rec walk c t =
        match t with
        | TmVar (x, n) ->
            if x = j + c then
                termShift c s
            else
                TmVar(x, n)
        | TmAbs (x, t1) -> TmAbs(x, walk (c + 1) t1)
        | TmApp (t1, t2) -> TmApp(walk c t1, walk c t2)

    walk 0 t

let termSubstTop s t =
    termShift (-1) (termSubst 0 (termShift 1 s) t)

let rec isval ctx t =
    match t with
    | TmAbs _ -> true
    | _ -> false

let rec eval1 ctx t =
    match t with
    | TmApp (TmAbs (x, t12), v2) when isval ctx v2 -> termSubstTop v2 t12 |> Some
    | TmApp (v1, t2) when isval ctx v1 ->
        let t2' = eval1 ctx t2
        Option.map (fun t2' -> TmApp(v1, t2')) t2'
    | TmApp (t1, t2) ->
        let t1' = eval1 ctx t1
        Option.map (fun t1' -> TmApp(t1', t2)) t1'
    | _ -> None

let rec eval ctx t =
    match eval1 ctx t with
    | Some t' -> eval ctx t'
    | None -> t

let ev = eval ()
