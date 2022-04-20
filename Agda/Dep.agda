open import Agda.Builtin.List 
open import Agda.Builtin.Nat
open import Agda.Builtin.Bool

map : {a : Set} → {b : Set} → (a → b) → List a → List b
map f []       = []
map f (x ∷ xs) = f x ∷ map f xs
