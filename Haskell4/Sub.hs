module Sub where

data Ty = Prim String
    | Lam Ty Ty
    | Rcd [(String, Ty)]
    | Top
    | Bot
    deriving (Show, Eq)

-- | subtype relationship
(<:) :: Ty -> Ty -> Bool
(Prim x)    <: (Prim y)    = x == y
x           <: Top         = True
Bot         <: y           = True
(Lam s1 s2) <: (Lam t1 t2) = t1 <: s2 && s2 <: t2
Rcd ts      <: Rcd ss      = all (`elemSub` ts) ss
  where
    elemSub (n, t) fs = case lookup n fs of
        Just s  -> t <: s
        Nothing -> False
_ <: _ = False

app :: Ty -> Ty -> Either String Ty
app (Lam p r) t | t <: p    = Right r
                | otherwise = Left $ show t ++ " is not subtype of " ++ show p
app _ _ = Left "Cannot apply to non-fun"

v1 :: Ty
v1 = Rcd [("x", Prim "int")]

v2 :: Ty
v2 = Rcd
    [ ("y", Prim "bool")
    , ("x", Prim "int")
    , ("z", Lam (Prim "int") (Prim "int"))
    ]

f1 :: Ty
f1 = Lam (Rcd [("x", Prim "int")]) (Prim "int")

f2 :: Ty
f2 = Lam (Rcd [("y", Prim "string")]) (Prim "unit")

-- >>> v2 <: v1
-- True
-- >>> app f1 v2
-- Right (Prim "int")
-- >>> app f2 v1
-- Left "Rcd [(\"x\",Prim \"int\")] is not subtype of Rcd [(\"y\",Prim \"string\")]"
