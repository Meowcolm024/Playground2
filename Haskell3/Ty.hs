{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE KindSignatures #-}

module Ty where

a = id @Int 3

b = id @(Int -> Int) (id @Int)

newtype MInt = MInt Int deriving (Show, Eq)

f :: Semigroup a => a -> a -> a
f x y = x <> y <> y <> x

instance Semigroup MInt where
  MInt i <> MInt j = MInt $ i + j
