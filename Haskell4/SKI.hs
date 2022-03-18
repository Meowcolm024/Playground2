module SKI where

data Term = I | K | S | App Term Term deriving Show

isval :: Term -> Bool
isval I                 = True
isval K                 = True
isval (App K v)         = isval v
isval S                 = True
isval (App S         v) = isval v
isval (App (App s v) u) = isval v && isval u
isval _                 = False

eval :: Term -> Term
eval (App I                 t) = t
eval (App (App K         v) _) = v
eval (App (App (App S x) y) z) = App (App x z) (App y z)
eval t | isval t   = t
       | otherwise = error "invalid"

-- >>> eval (App (App K I) (App I I))
-- I
