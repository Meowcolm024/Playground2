{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
module Expr where

data Expr a where
    LitInt  :: Int -> Expr Int
    LitBool :: Bool -> Expr Bool
    Pair    :: Expr p -> Expr q -> Expr (p, q)
    Fst     :: Expr (p, q) -> Expr p
    Snd     :: Expr (p, q) -> Expr q
    If      :: Expr Bool -> Expr b -> Expr b -> Expr b
    Add     :: Expr Int -> Expr Int -> Expr Int
    Sub     :: Expr Int -> Expr Int -> Expr Int
    IsZerp  :: Expr Int -> Expr Bool
    Not     :: Expr Bool -> Expr Bool

eval :: forall a . Expr a -> a
eval (LitInt  a) = a
eval (LitBool a) = a
eval (Pair f s ) = (eval f, eval s)
eval (Fst p    ) = fst (eval p)
eval (Snd p    ) = snd (eval p)
eval (If p x y ) = if eval p then eval x else eval y
eval (Add x y  ) = eval x + eval y
eval (Sub x y  ) = eval x - eval y
eval (IsZerp x ) = eval x == 0
eval (Not x    ) = not (eval x)

-- >>> eval $ Fst (Pair (LitInt 1) (LitBool True))
-- 1
