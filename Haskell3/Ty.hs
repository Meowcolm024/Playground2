{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE KindSignatures #-}

module Ty where

a = id @Int 3

b = id @(Int -> Int) (id @Int)
