type Term =
    | Lit of string
    | Abs of string * Term
    | App of Term * Term

let mutable idx = 0
let fresh() =
    idx <- idx + 1
    idx.ToString()
