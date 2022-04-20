module Graph where

type Node = Int
type Adj b = [(b, Node)]
type Context a b = (Adj b, Node, a, Adj b)  -- in, node, label, out

data Graph a b = Empty | (Context a b) :& (Graph a b) deriving Show
