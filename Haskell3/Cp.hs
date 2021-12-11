{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances #-}

module Cp where

data N = E | O

data Number (n :: N) where
    Odd ::Int -> Number O
    Even ::Int -> Number E

instance Show (Number E) where
    show (Even x) = "Even: " ++ show x

instance Show (Number O) where
    show (Odd x) = "Odd: " ++ show x

nOdd :: Int -> Number 'O
nOdd n | odd n     = Odd n
       | otherwise = error "not odd"

nEven :: Int -> Number 'E
nEven n | even n    = Even n
        | otherwise = error "not even"

class Add p q r | p q -> r where
    add :: Number p -> Number q -> Number r

instance Add E E E where
    add (Even x) (Even y) = Even (x + y)

instance Add O O E where
    add (Odd x) (Odd y) = Even (x + y)

instance Add O E O where
    add (Odd x) (Even y) = Odd (x + y)

instance Add E O O where
    add (Even x) (Odd y) = Odd (x + y)

-- >>> test
-- Even: 14
test = add (add x y) (add z w)
  where
    x = Odd 3
    y = Even 4
    z = Even 6
    w = Odd 1
