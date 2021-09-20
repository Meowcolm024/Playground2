module Haskell2.Formu where

import           Text.ParserCombinators.Parsec

data Expr = Raw Int
          | Div Int
          | Sin Int
          | Cos Int
          | DivSin Int
          | DivCos Int
          | Pow Int
          | Poly Int
          | Cons Expr Expr
          deriving Show

regularParse :: Parser a -> String -> Either ParseError a
regularParse p = parse p "(unknown)"

numbers :: Parser Expr
numbers = do
    i <- many1 digit
    return $ Raw (read i)

polys :: Parser Expr
polys = do
    i <- many digit
    string "x"
    return $ case i of
        [] -> Poly 1
        _ -> Poly (read i)

sins :: Parser Expr
sins = do
    i <- many digit
    string "sinx"
    return $ case i of
        [] -> Sin 1
        _ -> Sin (read i)

expr :: Parser Expr
expr = choice [try sins, try polys, numbers]

exprs :: Parser Expr
exprs = do
    x <- expr
    xs <- many $ do 
        char '+'
        expr
    return $ foldl Cons x xs
    