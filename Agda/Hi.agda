module Hi where

data Bool : Set where
    true : Bool
    false : Bool

data Nat : Set where
    zero : Nat
    succ : Nat -> Nat

infixl 40 _+_

_+_ : Nat -> Nat -> Nat
zero + n = n
succ m + n = succ (m + n)

infixr 40 _::_

data List (A : Set) : Set where
    [] : List A
    _::_ : A -> List A -> List A

_++_ : {A : Set} -> List A -> List A -> List A
[]        ++ ys = ys
(x :: xs) ++ ys = x :: (xs ++ ys)

data Vec (A : Set) : Nat -> Set where
    nil : Vec A zero
    cons : {n : Nat} -> A -> Vec A n -> Vec A (succ n)

head : {A : Set} {n : Nat} -> Vec A (succ n) -> A
head (cons h _) = h

tail : {A : Set} {n : Nat} -> Vec A (succ n) -> Vec A n
tail (cons _ t) = t

data Fin : Nat -> Set where
    fzero : {n : Nat} -> Fin (succ n)
    fsucc : {n : Nat} -> Fin n -> Fin (succ n)

data Empty : Set where
    empty : Fin zero -> Empty

_!_ : {n : Nat}{A : Set} -> Vec A n -> Fin n -> A
nil ! ()
(cons x _) ! fzero = x
(cons _ xs) ! (fsucc n) = xs ! n

test : Vec Nat (succ (succ zero))
test = cons (succ zero) (cons zero nil)

-- v1 : Nat
-- v1 = test ! (fsucc (fsucc fzero))

data False : Set where
record True : Set where

trivial : True
trivial = _

isTrue : Bool -> Set
isTrue true = True
isTrue false = False

_<_ : Nat -> Nat -> Bool
_ < zero = false
zero < (succ _) = true
(succ m) < (succ n) = m < n

length : {A : Set} -> List A -> Nat
length [] = zero
length (_ :: xs) = succ (length xs)

lookup : {A : Set}(xs : List A)(n : Nat) -> isTrue (n < length xs) -> A
lookup [] _ ()
lookup (x :: _) zero p = x
lookup (_ :: xs) (succ n) p = lookup xs n p

filter : {A : Set} -> (A -> Bool) -> List A -> List A
filter _ [] = []
filter p (x :: xs) with p x
... | true = x :: filter p xs
... | false = filter p xs

record Point : Set where
    field 
        x : Nat
        y : Nat

mkPoint : Nat -> Nat -> Point
mkPoint a b = record {x = a; y = b}
