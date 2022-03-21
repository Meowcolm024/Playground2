module Flt where

data Bit = I | O deriving(Show, Eq)

b2i I = 1
b2i O = 0

i2b 1 = I
i2b 0 = O

data Flt = Flt
    { exponent    :: [Bit]
    , significand :: [Bit]
    }
    deriving Show

-- >>> r
-- 65520
r = sum $ map (2^) [4..15]
