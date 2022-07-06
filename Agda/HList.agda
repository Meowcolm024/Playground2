open import Agda.Builtin.List 
open import Agda.Builtin.Nat
open import Agda.Builtin.Bool
open import Agda.Builtin.Char
open import Agda.Builtin.String
open import Agda.Builtin.Unit

data HList : List Set → Set where
  hnil  : HList []
  hcons : {x : Set} {xs : List Set} → x → HList xs → HList (x ∷ xs)

hd : {x : Set} {xs : List Set} → HList (x ∷ xs) → x
hd (hcons h _) = h

tl : {x : Set} {xs : List Set} → HList (x ∷ xs) → HList xs
tl (hcons _ t) = t

a : HList (Bool ∷ Nat ∷ Bool ∷ [])
a = hcons false (hcons 1 (hcons true hnil))

f : Bool → Set
f true = Bool
f false = Nat

btst : List Bool → List Set
btst [] = []
btst (x ∷ xs) = f x ∷ btst xs

initHList : (xs : List Bool) → HList (btst xs)
initHList [] = hnil
initHList (true ∷ xs) = hcons false (initHList xs)
initHList (false ∷ xs) = hcons 0 (initHList xs)
