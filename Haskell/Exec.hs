module Haskell.Exec where

import           Control.Monad
import           Data.Array.ST
import           Data.Array.Unboxed

-- >>> even . f $ [1,1,1,1]
-- False
f :: [Int] -> Int
f []       = 0
f [0     ] = 0
f [1     ] = 1
f (x : xs) = if x == 0 then f xs else 2 ^ length xs + f xs

dp :: [a] -> Bool
dp xs = result ! length xs
 where
  result = runSTUArray $ do
    mark <- newArray (0, length xs) False
    writeArray mark 0 True
    forM_ [1 .. length xs] $ \p -> do
      m <- readArray mark p
      when m $ forM_ [p .. length xs] $ \q ->
        when (something xs p q) $ writeArray mark q True
    return mark

something :: [a] -> Int -> Int -> Bool
something = undefined

-- >>> fib 100
-- 3736710778780434371
fib :: Int -> Int
fib n = result ! n
  where
    result = runSTUArray $ do
      fibs <- newArray (0, n) 0
      (fibs, 0) ~= 0
      (fibs, 1) ~= 1
      forM_ [2 .. n] $ \p -> do
        x <- readArray fibs (p - 1)
        y <- readArray fibs (p - 2)
        (fibs, p) ~= (x + y)
      return fibs

(arr, i) ~= e = writeArray arr i e
