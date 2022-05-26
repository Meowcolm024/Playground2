{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Haskell5.Ty where

fix :: (t -> t) -> t
fix f = let x = f x in x

-- >>> acc 10
-- 20
acc :: Integer -> Integer
acc = fix $ \f x -> if x == 0 then 0 else 2 + f (x - 1)

-- (fix (\f: Nat -> Nat. \x: Nat. if iszero x then 0 else succ succ (f (pred x)))) 5

-- letrec f: Nat -> Nat = (\x: Nat. if iszero x then 0 else succ succ (f (pred x))) in f 5

data Range = Range
    { start :: Int
    , end   :: Int
    , sep   :: Int
    }
    deriving (Show, Eq)

infixl `to`
to :: Int -> Int -> Range
x `to` y = Range x y 1

infixl `until`
until :: Int -> Int -> Range
x `until` y = Range x (y - 1) 1

infixl `by`
by :: Range -> Int -> Range
r `by` s = r { sep = s }

get :: Range -> [Int]
get (Range x y s) = x : tail (takeWhile (< y) (scanl (+) s [x ..]))

-- >>> get res
-- [3,5,9]
res = 3 `to` 10 `by` 2

{- 
let add: Nat*Nat->(Nat*Nat) = \x:Nat*Nat.{pred fst x, succ snd x } in 
let PLUS:Nat*Nat->(Nat*Nat) = \x:Nat*Nat. if iszero fst x then x else add x in 
    (\x:Nat*Nat. if iszero fst x then snd x else snd PLUS (add x)) {2,3}
 -}

add :: (Int, Int) -> (Int, Int)
add = \x -> (fst x - 1, snd x + 1)

plus :: (Int, Int) -> (Int, Int)
plus = \x -> if (fst x) == 0 then x else add x

-- >>> r
-- 5
r :: Int
r = (\x -> if (fst x) == 0 then snd x else snd (plus (add x))) (2, 3)

-- >>> cwr 7 5
-- 462
cwr :: Integer -> Integer -> Integer
cwr n r = product [n .. n + r - 1] `quot` product [1 .. r]

data PP p = PP
    { pair   :: forall a b . a -> b -> p a b
    , first  :: forall a b . p a b -> a
    , second :: forall a b . p a b -> b
    }

ppPair :: PP (,)
ppPair = PP (,) fst snd

-- >>> swapp ppPair (1,2)
-- (2,1)

swapp :: PP p -> p a b -> p b a
swapp (PP p f s) x = p (s x) (f x)

class ListLike where
    type T :: *
    type List :: * -> *
    hd :: List T -> T
    tl :: List T -> List T

instance ListLike where
    type T = Int
    type List = []
    hd = head
    tl = tail
