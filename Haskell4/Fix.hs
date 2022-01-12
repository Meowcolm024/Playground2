module Fix where

fix :: (t -> t) -> t
fix f = f (fix f)

data Fix f = Fix
    { unFix :: f (Fix f)
    }

-- List = u a. unit | nat * a  
data List' a list = Nil | Cons a list
type List a = Fix (List' a)

hd :: List a -> a
hd (Fix (Cons a _)) = a

fromList :: [a] -> List a
fromList = fix f
  where
    f g lst = case lst of
        []       -> Fix Nil
        (x : xs) -> Fix $ Cons x (g xs)

empty :: List a -> Bool
empty lst = case unFix lst of
    Nil -> True
    _   -> False

len :: List a -> Int
len = fix f
  where
    f g lst = case unFix lst of
        Nil       -> 0
        Cons _ tl -> 1 + g tl
