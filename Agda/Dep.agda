open import Agda.Builtin.List 
open import Agda.Builtin.Nat
open import Agda.Builtin.Bool
open import Agda.Builtin.Char
open import Agda.Builtin.String
open import Agda.Builtin.Unit


map : {a : Set} → {b : Set} → (a → b) → List a → List b
map f []       = []
map f (x ∷ xs) = f x ∷ map f xs

infixr 5 _++_

_++_ : ∀ {A : Set} → List A → List A → List A
[]       ++ ys  =  ys
(x ∷ xs) ++ ys  =  x ∷ (xs ++ ys)

record Monoid {a} (A : Set a) : Set a where
  field
    mempty : A
    _<>_   : A → A → A

-- instance
--   ListMonoid : ∀ {a} {A : Set a} → Monoid (List A)
--   ListMonoid = record { mempty = []; _<>_ = _++_ }

instance
    NatMonoid : Monoid Nat
    NatMonoid = record { mempty = 0; _<>_ = _+_ }

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

inRange : Nat → Bool
inRange x = (3 < x) && (9 < x)
  where
    _&&_ : Bool -> Bool -> Bool
    true && true = true
    true && false = false
    false && _ = false

fmt : List Char → List Set
fmt [] = []
fmt ('%' ∷ 'd' ∷ xs) = Nat ∷ fmt xs
fmt ('%' ∷ 's' ∷ xs) = String ∷ fmt xs
fmt (x ∷ xs) = fmt xs

fmts : String → List Set
fmts s = fmt (primStringToList s)
