module Lc where

nil c n = n

cons h t c n = c h (t c n)

tolist l = l (:) []

fromlist xs = foldr cons nil xs

mapl f l = l (cons . f) nil

len l = l (const (+1)) 0

suml l = l (+) 0

append l r c n = l c (r c n)

exists p l = l ((||) . p) False

l1 = cons 1 (cons 2 (cons 3 nil))

-- >>> exists (<=2) l1
-- True
