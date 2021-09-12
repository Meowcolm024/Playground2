{-# LANGUAGE RankNTypes #-}
module Haskell.Regex where

-- ! matched info lost
data Result = A     -- ^ Accepted
            | O     -- ^ Objected
            | P     -- ^ Pending
            deriving Show

data RegEx a = Epsilon
             | Atom a
             | Or (RegEx a) (RegEx a)
             | Then (RegEx a) (RegEx a)
             | Star (RegEx a)
             deriving Show

type RegMatch a = forall a . Eq a => RegEx a -> [a] -> (Result, [a])

(+++) :: (Result, [a]) -> (Result, [a]) -> (Result, [a])
rx@(A, _) +++ _         = rx
(   P, _) +++ ry@(A, _) = ry
_         +++ ry        = ry

-- ! seems not able to handle nested stars
matchRegEx :: RegMatch a
matchRegEx Epsilon []                 = (A, [])
matchRegEx Epsilon es                 = (P, es)
matchRegEx (Atom x) (e : es) | x == e = (A, es)
matchRegEx (Or rx ry) es              = matchRegEx rx es +++ matchRegEx ry es
matchRegEx (Then rx ry) es
    | (A, es') <- matchRegEx rx es = matchRegEx ry es'
    | (P, es') <- matchRegEx rx es = matchRegEx ry es'
matchRegEx (Star _) [] = (A, [])
matchRegEx s@(Star r) es | (A, []) <- result  = (A, [])
                         | (A, es') <- result = matchRegEx s es'
                         | (O, es') <- result = (P, es')
    where result = matchRegEx r es
matchRegEx _ es = (O, es)

match :: RegMatch a
match r e | (A, x@(_ : _)) <- result = (O, x)
          | (P, x) <- result         = (O, x)
          | otherwise                = result
    where result = matchRegEx r e

-- >>> match zeros [0,1,0,0]
-- (A,[])
zeros :: RegEx Int
zeros = Then (Then (Atom 0) (Or (Atom 1) Epsilon)) (Star (Atom 0))

-- >>> match aabbs "abbbb"
-- (A,"")
aabbs :: RegEx Char
aabbs = Then (Star (Atom 'a')) (Star (Atom 'b'))

alpha :: RegEx Char
alpha = foldl1 Or . map Atom $ ['a' .. 'z'] ++ ['0' .. '9']

-- >>> match email "helloworld@mail.com"
-- (A,"")
email :: RegEx Char
email = Then (Then alphas (Atom '@')) (Then alphas (Then (Atom '.') alphas))
    where alphas = Then alpha (Star alpha)

-- >>> match (Star (Then (Atom 0) (Atom 1))) [0,1,0,1,0,1]
-- (A,[])
-- >>> match alpha "a1"
-- (O,"1")
