{-# LANGUAGE ForeignFunctionInterface #-}
module HSLib where

import           Foreign.C.Types

-- ghc -c -O HsLib.hs

fibonacci :: Int -> Int
fibonacci n = fibs !! n
    where fibs = 0 : 1 : zipWith (+) fibs (tail fibs)

fibonacci_hs :: CInt -> CInt
fibonacci_hs = fromIntegral . fibonacci . fromIntegral

foreign export ccall fibonacci_hs :: CInt -> CInt
