module AVL where

data AVLTree a = Empty | Br (AVLTree a) a (AVLTree a) Int deriving (Show)

insert :: Ord a => AVLTree a -> a -> AVLTree a
insert t x = fst $ ins t
  where
    ins Empty = (Br Empty x Empty 0, 1)
    ins (Br l k r d) | x < k     = tree (ins l) k (r, 0) d
                     | x == k    = (Br l k r d, 0)
                     | otherwise = tree (l, 0) k (ins r) d

tree :: (AVLTree a, Int) -> a -> (AVLTree a, Int) -> Int -> (AVLTree a, Int)
tree (l, dl) k (r, dr) d = balance (Br l k r d', delta)  where
    d'    = d + dr - dl
    delta = deltaH d d' dl dr

deltaH :: Int -> Int -> Int -> Int -> Int
deltaH d d' dl dr | d >= 0 && d' >= 0 = dr
                  | d <= 0 && d' >= 0 = d + dr
                  | d >= 0 && d' < 0  = dl - d
                  | otherwise         = dl

balance :: (AVLTree a, Int) -> (AVLTree a, Int)
balance (Br (Br (Br a x b dx) y c (-1)) z d (-2), _) =
    (Br (Br a x b dx) y (Br c z d 0) 0, 0)
balance (Br a x (Br b y (Br c z d dz) 1) 2, _) =
    (Br (Br a x b 0) y (Br c z d dz) 0, 0)
balance (Br (Br a x (Br b y c dy) 1) z d (-2), _) =
    (Br (Br a x b dx') y (Br c z d dz') 0, 0)  where
    dx' = if dy == 1 then -1 else 0
    dz' = if dy == -1 then 1 else 0
balance (Br a x (Br (Br b y c dy) z d (-1)) 2, _) =
    (Br (Br a x b dx') y (Br c z d dz') 0, 0)  where
    dx' = if dy == 1 then -1 else 0
    dz' = if dy == -1 then 1 else 0
balance (t, d) = (t, d)

fromList :: Ord a => [a] -> AVLTree a
fromList = foldl insert Empty
