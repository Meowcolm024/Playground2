open import Agda.Builtin.Bool
open import Agda.Builtin.Maybe

infixl 4 _<$>_
_<$>_ : {A B : Set} → (A → B) → Maybe A → Maybe B
f <$> nothing   = nothing
f <$> (just v)  = just (f v)

data Term : Set where
    true            : Term
    false           : Term
    zero            : Term
    succ            : Term → Term
    pred            : Term → Term
    iszero          : Term → Term
    if_then_else_   : Term → Term → Term → Term

isnv : Term → Bool
isnv zero       = true
isnv (succ n)   = isnv n
isnv _          = false

reduce : Term → Maybe Term
reduce (if true  then t1 else _ )   = just t1
reduce (if false then _  else t2)   = just t2
reduce (if p     then t1 else t2)   = ( λ p' → if p' then t1 else t2 ) <$> reduce p
reduce (succ n)                     = succ <$> reduce n
reduce (pred zero)                  = just zero
reduce (pred (succ n)) with (isnv n)
... | true                          = just n
... | false                         = nothing
reduce (pred n)                     = pred <$> reduce n
reduce (iszero zero)                = just true
reduce (iszero (succ n)) with (isnv n)
... | true                          = just false
... | false                         = nothing
reduce (iszero n)                   = iszero <$> reduce n
reduce _                            = nothing 

{-# TERMINATING #-}
eval : Term → Term
eval t with (reduce t)
... | nothing = t
... | just t' = eval t'

t1 : Term
t1 = if (if iszero zero then false else true) then succ zero else succ (succ zero)
