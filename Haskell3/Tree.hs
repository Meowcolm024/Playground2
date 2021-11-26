module Tree where

data Tree a = Leaf | Node a (Tree a) (Tree a) deriving (Show, Eq)

insert :: Ord a => Tree a -> a -> Tree a
insert Leaf x = Node x Leaf Leaf
insert t@(Node v l r) x | v > x     = Node v (insert l x) r
                        | v < x     = Node v l (insert r x)
                        | otherwise = t

delete :: Ord a => Tree a -> a -> Tree a
delete Leaf _ = Leaf
delete t@(Node v l r) x
    | v > x = Node v (delete l x) r
    | v < x = Node v l (delete r x)
    | otherwise = case delMax r of
        Nothing     -> l
        Just (m, z) -> Node m l z
  where
    delMax Leaf            = Nothing
    delMax (Node v l Leaf) = Just (v, l)
    delMax (Node v l r   ) = do
        (m, z) <- delMax r
        pure (m, Node v l z)

fromList :: Ord a => [a] -> Tree a
fromList = foldl insert Leaf
