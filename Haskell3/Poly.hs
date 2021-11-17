module Poly where

import           Control.Monad
import           Control.Monad.ST
import           Control.Monad.Trans.State
import           Data.Functor
import           Data.STRef

countTrue :: [Bool] -> Int
countTrue arr = runST $ do
    i <- newSTRef 0
    forM_ arr $ \n -> do
        when n $ modifySTRef i (+ 1)
    readSTRef i

data Tree = Leaf Int | Node Tree Tree deriving Show

countPos tree = do
    n <- get
    case tree of
        Leaf i   -> when (i > 0) $ put (n + 1)
        Node l r -> countPos l *> countPos r

test = Node (Node (Leaf 1) (Node (Leaf (-1)) (Leaf 3)))
            (Node (Node (Leaf (-4)) (Leaf (-2))) (Leaf 4))

resutl = execState (countPos test) 0

isort []       = []
isort (x : xs) = ist x (isort xs)
  where
    ist y []       = [y]
    ist t (y : ys) = if t < y then t : y : ys else y : ist t ys
