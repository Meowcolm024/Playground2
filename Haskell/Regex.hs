{-# LANGUAGE RankNTypes #-}
module Haskell.Regex where

data Result = A | O | P deriving Show

data RegEx a = Epsilon
             | Atom a
             | Or (RegEx a) (RegEx a)
             | Then (RegEx a) (RegEx a)
             | Star (RegEx a)
             deriving Show

type RegChr = RegEx Char
type RegInt = RegEx Int
type RegMatch a = forall a . Eq a => RegEx a -> [a] -> (Result, [a])

(+++) :: (Result, [a]) -> (Result, [a]) -> (Result, [a])
rx@(A, _) +++ _         = rx
(   P, _) +++ ry@(A, _) = ry
_         +++ ry        = ry

matchRegEx :: RegMatch a
matchRegEx Epsilon []                 = (A, [])
matchRegEx Epsilon es                 = (P, es)
matchRegEx (Atom x) (e : es) | x == e = (A, es)
matchRegEx (Or rx ry) es              = matchRegEx rx es +++ matchRegEx ry es
matchRegEx (Then rx ry) es
    | (A, es') <- matchRegEx rx es = matchRegEx ry es'
    | (P, es') <- matchRegEx rx es = matchRegEx ry es'
matchRegEx (Star _) [] = (A, [])
matchRegEx s@(Star r) es | (A, []) <- matchRegEx r es  = (A, [])
                         | (A, es') <- matchRegEx r es = matchRegEx s es'
                         | (O, es') <- matchRegEx r es = (P, es')
matchRegEx _ es = (O, es)

match :: RegMatch a
match r e | (A, x@(_ : _)) <- result = (O, x)
          | (P, x) <- result         = (O, x)
          | otherwise                = result
    where result = matchRegEx r e

-- >>> match zeros [0,1,0,0]
-- (A,[])
zeros :: RegInt
zeros = Then (Then (Atom 0) (Or (Atom 1) Epsilon)) (Star (Atom 0))

aabbs :: RegChr
aabbs = Then (Star (Atom 'a')) (Atom 'b')

-- >>> match (Star (Then (Atom 0) (Atom 1))) [0,1,0,1,0,1]
-- (A,[])
