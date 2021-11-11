{-# LANGUAGE RankNTypes #-}

module Fa where

h :: (a -> b) -> a -> b
h x y = x y

f :: (forall a. a -> a) -> b -> b
f x y = x y

g :: (forall a b. a -> b) -> c -> d
g x y = x y

w :: Num c => (forall a b. Num b => a -> b) -> c
w x = x x

r :: (forall a b. a -> b) -> c
r x = x x x x x x x

k :: (forall a b. a -> b) -> t1 -> t2 -> (t3 -> t4 -> t5) -> t5
k x y z f = f (x y) (x z)

fun :: (forall a. a) -> (forall a. a) -> (forall a. a) -> (forall a. a)
fun i j k = i (i j) (k j j) k i

-- * WHAT ???????
d :: (forall a. a) -> (forall a. a)
d x = x x

-- >>> c (*2) 6 3.14 (,)
-- (12,6.28)
c :: (Num t1, Num t2) => (forall a. Num a => a -> a) -> t1 -> t2 -> (t1 -> t2 -> t3) -> t3
c x y z f = f (x y) (x z)

-- >>> appBoth (+1) (3, 4.5)
-- (4,5.5)
appBoth :: (Num a, Num b) => (forall a. Num a => a -> a) -> (a, b) -> (a, b)
appBoth f (x, y) = (f x, f y)

-- >>> z
-- 3
z :: Integer
z = w (const 3)

-- fact :: Int -> Int
-- fact n = fact' n fact'
--     where
--         fact' :: Int -> (forall a. Int -> a -> Int) -> Int
--         fact' 0 _ = 1
--         fact' x f = x * f (x-1) f
