module Bn where

import           Data.Char

data Sig = Pos | Neg deriving (Show, Eq)

data Bn = Bn
    { num :: [Int]
    , len :: Int
    , sig :: Sig
    }
    deriving Eq

instance Show Bn where
    show (Bn n _ s) = (if s == Neg then "-" else "") ++ map intToDigit n

instance Num Bn where
    (+) = undefined

    (*) = undefined

    signum (Bn [0] 1 _  ) = Bn [0] 1 Pos
    signum (Bn _   _ Pos) = Bn [1] 1 Pos
    signum (Bn _   _ Neg) = Bn [1] 1 Neg

    abs (Bn n l _) = Bn n l Pos

    negate (Bn n l Pos) = Bn n l Neg
    negate (Bn n l Neg) = Bn n l Pos

    fromInteger x = case bn $ show x of
        Just x' -> x'
        Nothing -> Bn [0] 1 Pos

bn :: String -> Maybe Bn
bn ('-' : x) = negate <$> parseBn x
bn x         = parseBn x

parseBn :: String -> Maybe Bn
parseBn x = if all (`elem` ['0' .. '9']) x
    then Just $ Bn (map digitToInt x) (length x) Pos
    else Nothing

