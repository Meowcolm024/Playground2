module Haskell.BackTracking where

import           Data.List

for :: Functor f => f a -> (a -> b) -> f b
for = flip fmap

-- >>> subsetSum [8,6,7,5,3,10,9] 15
-- True
-- >>> subsetSum [11,6,5,1,7,13,12] 15
-- False
subsetSum :: [Int] -> Int -> Bool
subsetSum _  0 = True
subsetSum [] _ = False
subsetSum xs t = t > 0 && or
  [ subsetSum (x `delete` xs) (t - x) || subsetSum (x `delete` xs) t | x <- xs ]

-- >>> constructSubset [8,6,7,5,3,10,9] 15
-- [[8,7],[6,9],[7,5,3],[5,10]]
constructSubset :: [Int] -> Int -> [[Int]]
constructSubset _  0        = [[]]
constructSubset [] _        = []
constructSubset _ t | t < 0 = []
constructSubset (x : xs) t  = map (x :) y `union` z
 where
  y = constructSubset xs (t - x)
  z = constructSubset xs t

-- >>> map isWord ["123", "233332"]
-- [False,True]
isWord' :: String -> Bool
isWord' xs = length xs >= 3 && xs == reverse xs

-- >>> splittable "12332112210"
-- False
splittable :: (String -> Bool) -> String -> Bool
splittable _      [] = True
splittable isWord xs = or $ for [1 .. length xs] $ \i ->
  isWord (take i xs) && splittable isWord (drop i xs)

