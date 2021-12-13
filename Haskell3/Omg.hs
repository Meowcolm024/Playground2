{-# LANGUAGE RankNTypes #-}

f :: (forall a. a) -> (forall a. a)
f = \x -> x x

g x y z f = f (x y) (x z)
