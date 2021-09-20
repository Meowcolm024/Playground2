module Haskell.Solver where

type Map = [[Int]]
type Move = [Int]
type Score = Int

-- do the swap and matches
doMove :: Map -> Move -> (Map, Score)
doMove = undefined

-- generate the best next move
consider :: Map -> Maybe ([Move], Score)
consider mp = undefined
  where
    len = length mp
    helper :: [Move] -> Move -> Score -> ([Move], Score)
    helper pr mv sc | (_, s) <- doMove mp mv =
        if s > sc then ([mv], s) else if s == sc then (mv : pr, sc) else (pr, sc)


solver :: Map -> Maybe (Move, Score)
solver mp = case consider mp of
    Nothing              -> Nothing -- no move possible
    Just ([move], score) -> Just (move, score)
    Just (moves , score) -> undefined where moved = map (fst . doMove mp) moves

