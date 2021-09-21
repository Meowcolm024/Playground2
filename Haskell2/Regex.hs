{-# LANGUAGE RankNTypes #-}
module Haskell2.Regex where

import           Control.Applicative

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

derive :: Eq a => a -> RegEx a -> RegEx a
derive c = work
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
accepts e (c : w) = accepts (derive c e) w

derivatives :: Eq a => RegEx a -> [a] -> Maybe (RegEx a)
derivatives = (valid .) . foldl (flip derive)
 where
  valid Failure      = Nothing
  valid Epsilon      = Just Epsilon
  valid a@(Atom _  ) = Just a
  valid (  Or   p q) = valid p <|> valid q
  valid (  Then p q) = Then <$> valid p <*> valid q
  valid (  Star s  ) = Star <$> valid s

-- >>> accepts zeros [0,0,0,1,0]
-- False
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

t1, t2, t3, t4 :: RegEx Char
t1 = Then (Atom 'a') (Star (Then (Atom 'a') (Atom 'b')))
t2 = Then (Star (Atom 'b')) (Star (Then (Atom 'a') (Atom 'c')))
t3 = Then (Atom 'c') (Then (Atom 'b') (Atom 'a'))
t4 = Then (Atom 'c') (Star (Atom 'c'))
