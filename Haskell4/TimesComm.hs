{-# LANGUAGE TypeOperators, TypeFamilies, GADTs, UndecidableInstances #-}

module TimesComm where

-- import Kata.TimesComm.Definitions

-- {- Preloaded code. Maybe helpful for local editing.

-- | The natural numbers, encoded in types.
data Z
data S n

-- | Predicate describing natural numbers.
-- | This allows us to reason with `Nat`s.
data Natural :: * -> * where
  NumZ :: Natural Z
  NumS :: Natural n -> Natural (S n)

-- | Predicate describing equality of natural numbers.
data Equal :: * -> * -> * where
  EqlZ :: Equal Z Z
  EqlS :: Equal n m -> Equal (S n) (S m)

-- | Peano definition of addition.
type family (:+:) (n :: *) (m :: *) :: *
type instance Z :+: m = m
type instance S n :+: m = S (n :+: m)

-- | Peano definition of multiplication.
type family (:*:) (n :: *) (m :: *) :: *
type instance Z :*: m = Z
type instance S n :*: m = m :+: (n :*: m)

-- -}

-- This will be helpful
plus' :: Equal n m -> Natural a -> Equal (n :+: a) (m :+: a)
plus' = undefined

-- | You need this! Copy your solution from
-- https://www.codewars.com/kata/a-plus-b-plus-c-equals-a-plus-b-plus-c-prove-it/haskell
plusAssoc :: Natural a -> Natural b -> Natural c -> Equal (a :+: (b :+: c)) ((a :+: b) :+: c)
plusAssoc = undefined

-- | You need this! Copy your solution from
-- https://www.codewars.com/kata/a-plus-b-equals-b-plus-a-prove-it/haskell
plusComm :: Natural a -> Natural b -> Equal (a :+: b) (b :+: a)
plusComm = _

-- This will also be helpful
zeroComm :: Natural a -> Equal Z (a :*: Z)
zeroComm = undefined

-- This is the proof that the kata requires.
-- | a * b = b * a
timesComm :: Natural a -> Natural b -> Equal (a :*: b) (b :*: a)
timesComm = undefined