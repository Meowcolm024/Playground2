module RecTy where

data Ty = Prim String   -- ^ primitive
    | Var Int           -- ^ variable
    | Ty :-> Ty         -- ^ lambda
    | Int :. Ty         -- ^ rec
    | Ty :| Ty          -- ^ sum
    | Ty :* Ty          -- ^ product
    deriving (Show, Eq)

infixl 8 :*
infixl 7 :|
infixr 6 :->
infixr 5 :.

-- | check if there're unbounded type variable
check :: Ty -> Bool
check = check' []
  where
    check' :: [Int] -> Ty -> Bool
    check' ctx ty = case ty of
        Prim s  -> True
        Var  n  -> n `elem` ctx
        t :-> s -> check' ctx t && check' ctx s
        n :.  t -> n `notElem` ctx && check' (n : ctx) t
        t :|  s -> check' ctx t && check' ctx s
        t :*  s -> check' ctx t && check' ctx s

-- >>> unfold list
-- Prim "unit" :| Prim "int" :* (0 :. Prim "unit" :| Prim "int" :* Var 0)
-- >>>  unfold $ unfold hungry
-- Prim "nat" :-> (Prim "nat" :-> (0 :. Prim "nat" :-> Var 0))
-- | unfold one step
unfold :: Ty -> Ty
unfold = uf []
  where
    uf :: [(Int, Ty)] -> Ty -> Ty
    uf ctx ty = case ty of
        Prim s  -> Prim s
        Var  n  -> let Just t = lookup n ctx in t
        t :-> s -> uf ctx t :-> uf ctx s
        n :.  t -> uf ((n, ty) : ctx) t
        t :|  s -> uf ctx t :| uf ctx s
        t :*  s -> uf ctx t :* uf ctx s

-- >>> check list
-- True
list :: Ty
list = 0 :. Prim "unit" :| Prim "int" :* Var 0

-- >>> unfold tree
-- Prim "unit" :| (Prim "nat" :* (0 :. Prim "unit" :| (Prim "nat" :* Var 0) :* Var 0)) :* (0 :. Prim "unit" :| (Prim "nat" :* Var 0) :* Var 0)
tree :: Ty
tree = 0 :. Prim "unit" :| Prim "nat" :* Var 0 :* Var 0

-- >>> unfold hd
-- Prim "unit" :| Prim "int" :* (0 :. Prim "unit" :| Prim "int" :* Var 0) :-> Prim "int"
hd :: Ty
hd = list :-> Prim "int"

-- >>> check hungry
-- True
hungry :: Ty
hungry = 0 :. Prim "nat" :-> Var 0

-- >>> unfold stream
-- Prim "unit" :-> Prim "nat" :* (0 :. Prim "unit" :-> Prim "nat" :* Var 0)
stream :: Ty
stream = 0 :. Prim "unit" :-> Prim "nat" :* Var 0
