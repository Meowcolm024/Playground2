module RBTree where

data Color = R | B deriving (Show)
data RBTree a = Empty | Node Color (RBTree a) a (RBTree a) deriving (Show)

insert :: Ord a => RBTree a -> a -> RBTree a
insert t x = makeBlack $ ins t
  where
    ins Empty = Node R Empty x Empty
    ins (Node color l k r) | x < k     = balance color (ins l) k r
                           | otherwise = balance color l k (ins r)

    makeBlack ~(Node _ l k r) = Node B l k r

balance :: Color -> RBTree a -> a -> RBTree a -> RBTree a
balance B (Node R (Node R a x b) y c) z d =
    Node R (Node B a x b) y (Node B c z d)
balance B (Node R a x (Node R b y c)) z d =
    Node R (Node B a x b) y (Node B c z d)
balance B a x (Node R b y (Node R c z d)) = 
    Node R (Node B a x b) y (Node B c z d)
balance B a x (Node R (Node R b y c) z d) =
    Node R (Node B a x b) y (Node B c z d)
balance color l k r = Node color l k r

fromList :: Ord a => [a] -> RBTree a
fromList = foldl insert Empty
