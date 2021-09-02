module Hello where

import           Control.Monad                  ( forM_ )

data Color = Red | Black

instance Show Color where
    show Red   = "red"
    show Black = "black"

invert :: Color -> Color
invert Red   = Black
invert Black = Red

qsort :: [Int] -> [Int]
qsort ys = case ys of
    []       -> []
    (x : xs) -> filter (<= x) xs ++ [x] ++ filter (> x) xs

class MyShow a where
    myShow :: a -> IO ()

    heShow :: a -> Int -> IO ()
    heShow x i = forM_ [0..i] $
        \_ -> myShow x

data Yky = Yky

instance MyShow Yky where
    myShow Yky = putStrLn "hello"

data Rat = Rat Int Int

instance Show Rat where
    show (Rat p q) = show p ++ "/" ++ show q

rat :: Int -> Int -> Rat
rat p q = let x = gcd p q in Rat (p `div` x) (q `div` x)
