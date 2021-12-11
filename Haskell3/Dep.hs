{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Dep where

data Nat = O | S Nat

data Vec (n :: Nat) a where
    Nil ::Vec O a
    Cons ::a -> Vec n a -> Vec (S n) a

class Len l where
    len :: Vec l a -> Int

instance Len O where
    len _ = 0

instance Len n => Len (S n) where
    len (Cons _ tl) = 1 + len tl

head' :: Vec (S n) a -> a
head' (Cons h _) = h

tail' :: Vec (S n) a -> Vec n a
tail' (Cons _ tl) = tl

-- >>> len test
-- 3
test :: Vec (S (S (S O))) Integer
test = Cons 1 (Cons 2 (Cons 3 Nil))
