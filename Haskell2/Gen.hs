{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}

module Haskell2.Gen where

import           GHC.Generics

data Bit = I | O deriving (Show, Generic)


-- flipT :: (U1 :+: U1) p -> (U1 :+: U1) p
-- flipT ::  Generic a => a -> a

flipT :: Generic a => a -> a
flipT = to . flip' . from
    where
        flip' (M1 (R1 (M1 U1))) = M1 (L1 (M1 U1))
        flip' (M1 (L1 (M1 U1))) = M1 (R1 (M1 U1))