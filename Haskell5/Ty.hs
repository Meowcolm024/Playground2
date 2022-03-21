{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}

module Ty where

data Tag = T | F deriving (Show)

data TyErr :: Tag -> * -> * where
    Safe ::a -> TyErr F a
    UnSafe ::a -> TyErr T a

app :: (a -> b -> c) -> TyErr F a -> TyErr F b -> TyErr F c
app f (Safe x) (Safe y) = Safe (f x y)
