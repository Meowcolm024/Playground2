{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
module Pord where

data Nat = Z | S Nat deriving (Show)

data TNat :: Nat -> * where
    TZ ::TNat Z
    TS ::TNat n -> TNat (S n)

deriving instance Show (TNat n)

data Vec :: Nat -> * -> * where
    Nil ::Vec Z a
    Cons ::a -> Vec n a -> Vec (S n) a

deriving instance Show a => Show (Vec n a)

type family   Add (n :: Nat) (m :: Nat) :: Nat
type instance Add Z m = m
type instance Add (S n) m = S (Add n m)

vhead :: Vec (S n) a -> a
vhead (Cons x _) = x

vtail :: Vec (S n) a -> Vec n a
vtail (Cons _ xs) = xs

len :: Vec n a -> TNat n
len Nil         = TZ
len (Cons _ xs) = TS (len xs)

fromList :: TNat n -> [a] -> Vec n a
fromList TZ     _        = Nil
fromList (TS n) (x : xs) = Cons x (fromList n xs)
fromList (TS n) []       = undefined

append :: Vec n a -> Vec m a -> Vec (Add n m) a
append Nil         ys = ys
append (Cons x xs) ys = Cons x (append xs ys)

instance Functor (Vec n) where
    fmap _ Nil         = Nil
    fmap f (Cons x xs) = Cons (f x) (fmap f xs)

four = TS (TS (TS (TS TZ)))
v4 = fromList four [1 .. 4]

x1 = vhead v4
x2 = vtail (vtail (vtail v4))
