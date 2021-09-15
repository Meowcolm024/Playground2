{-# LANGUAGE RankNTypes #-}
module Haskell.Regex where

data RegEx a = Failure
             | Epsilon
             | Atom a
             | Or (RegEx a) (RegEx a)
             | Then (RegEx a) (RegEx a)
             | Star (RegEx a)
             deriving Show

nullable :: RegEx a -> Bool
nullable Failure    = False
nullable Epsilon    = True
nullable (Atom _  ) = False
nullable (Or   p q) = nullable p || nullable q
nullable (Then p q) = nullable p && nullable q
nullable (Star _  ) = True

isProductive :: RegEx a -> Bool
isProductive Failure    = False
isProductive (Then p q) = isProductive p && isProductive q
isProductive (Or   p q) = isProductive p || isProductive q
isProductive _          = True

derive :: Eq a => RegEx a -> a -> RegEx a
derive reg c = work reg
 where
  work Failure  = Failure
  work Epsilon  = Failure
  work (Atom x) = if x == c then Epsilon else Failure
  work (Or p q) = Or (work p) (work q)
  work (Then p q) =
    let w = Then (work p) q in if nullable p then Or w (work q) else w
  work (Star s) = Then (work s) (Star s)

accepts :: Eq a => RegEx a -> [a] -> Bool
accepts e []      = nullable e
accepts e (c : w) = accepts (derive e c) w

-- >>> accepts zeros [0]
-- True
zeros :: RegEx Int
zeros = Then (Then (Atom 0) (Or (Atom 1) Epsilon)) (Star (Atom 0))

-- >>> accepts aabbs "abbaa"
-- False
aabbs :: RegEx Char
aabbs = Then (Star (Atom 'a')) (Star (Atom 'b'))

alpha :: RegEx Char
alpha = foldl1 Or . map Atom $ ['a' .. 'z'] ++ ['0' .. '9']

email :: RegEx Char
email = Then (Then alphas (Atom '@')) (Then alphas (Then (Atom '.') alphas))
  where alphas = Then alpha (Star alpha)
