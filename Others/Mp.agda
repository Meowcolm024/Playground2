module Mp where

open import Agda.Builtin.IO using (IO)
open import Agda.Builtin.Unit using (⊤)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.List 
open import Agda.Builtin.Nat

data Key (A : Set) : String -> Set where
    key : {k : String} -> A -> Key A k

data Map (A : Set) : List String -> Set where
    empty : Map A []
    put : {xs : List String} {x : String} -> Key A x -> Map A xs -> Map A (x ∷ xs)

get : {A : Set} {xs : List String} {x : String} -> Map A (x ∷ xs) -> Key A x
get (put k _) = k

m1 : Map Nat ("hello" ∷ [])
m1 = put (key 3) empty

m2 : Map Nat ("world" ∷ "hello" ∷ [])
m2 = put (key 10) m1

r1 : Key Nat "world"
r1 = get m2

r2 : Key Nat "hello"
r2 = get m1

postulate putStrLn : String → IO ⊤
{-# FOREIGN GHC import qualified Data.Text as T #-}
{-# COMPILE GHC putStrLn = putStrLn . T.unpack #-}

main : IO ⊤
main = putStrLn "Hello world!"
