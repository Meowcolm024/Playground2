{-# LANGUAGE MonadComprehensions #-}
{-# LANGUAGE ApplicativeDo #-}
module Appp where
import           Control.Applicative            ( Alternative((<|>), empty) )

newtype Parser a = Parser {parse :: String -> Maybe (a, String)}

instance Functor Parser where
    fmap f (Parser p) = Parser $ \s -> [ (f a, s') | (a, s') <- p s ]

instance Applicative Parser where
    pure a = Parser $ \s -> pure (a, s)
    (Parser f) <*> (Parser p) =
        Parser $ \s -> [ (a b, s'') | (a, s') <- f s, (b, s'') <- p s' ]

instance Alternative Parser where
    empty = Parser $ const Nothing
    (Parser a) <|> (Parser b) = Parser $ \s -> a s <|> b s

satisfy :: (Char -> Bool) -> Parser Char
satisfy p = Parser $ \xs -> case xs of
    []       -> Nothing
    (s : ss) -> [ (s, ss) | p s ]

char :: Char -> Parser Char
char c = satisfy (== c)

many :: Parser a -> Parser [a]
many p = Parser $ \s -> case parse p s of
    Nothing      -> Just ([], s)
    Just (a, s') -> case parse (many p) s' of
        Nothing        -> Just ([a], s')
        Just (a', s'') -> Just (a : a', s'')

many1 :: Parser a -> Parser [a]
many1 p = (:) <$> p <*> many p

string :: String -> Parser String
string = traverse char

choice :: Alternative f => [f a] -> f a
choice = foldr (<|>) empty

oneOf :: String -> Parser Char
oneOf = choice . map char

spaces :: Parser ()
spaces = many (oneOf " \n\t") *> pure ()

digits :: Parser String
digits = many1 $ oneOf ['0' .. '9']

option :: a -> Parser a -> Parser a
option a p = Parser $ \s -> case parse p s of
    Nothing      -> Just (a, s)
    Just (r, s') -> Just (r, s')

expr :: Parser Int
expr = flip ($) <$> factor <*> expr'

expr' :: Parser (Int -> Int)
expr' =
    (\d f i -> f (i + d))
        <$> (char '+' *> factor)
        <*> expr'
        <|> (\d f i -> f (i - d))
        <$> (char '-' *> factor)
        <*> expr'
        <|> pure id

factor :: Parser Int
factor = flip ($) <$> term <*> factor'

factor' :: Parser (Int -> Int)
factor' =
    (\d f i -> f (i * d))
        <$> (char '*' *> term)
        <*> expr'
        <|> (\d f i -> f (i `div` d))
        <$> (char '/' *> term)
        <*> expr'
        <|> pure id

term :: Parser Int
term = (read <$> digits) <|> char '(' *> expr <* char ')'

math :: String -> Maybe Int
math s = fst <$> parse expr s

-- >>> math "(1+2)*(4/2)+6/(3-1)"
-- >>> (1+2)*(4/2)+6/(3-1)
-- Just 9
-- 9.0

-- >>> parse ab "aaabc"
-- Just (("aaa","b"),"c")
ab = (,) <$> many (char 'a') <*> many (char 'b')

-- >>> parse float "3.14"
-- >>> parse float "233"
-- Just (3.14,"")
-- Just (233.0,"")
float :: Parser Float
float = do
    d <- digits
    s <- option "0" (char '.' *> digits)
    pure $ read $ d ++ "." ++ s

identifier = many1 $ oneOf ['a'..'z']
symbol s = spaces *> string s <* spaces

-- >>> parse ifElse " if true then 233 else 666 "
-- Just (("true","233","666")," ")
ifElse = do
    symbol "if"
    i <- identifier
    symbol "then"
    t <- digits
    symbol "else"
    r <- digits
    pure (i, t, r)
