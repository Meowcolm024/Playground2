import           Control.Monad
import           Control.Monad.Trans.State

type Program = State Machine ()

data Machine = Machine
    { stack     :: [Int]
    , registers :: [Int]
    , branches  :: [(String, Program)]
    }

machine :: Machine
machine = Machine [] [0, 0, 0, 0, 0] []

replaceNth :: Int -> a -> [a] -> [a]
replaceNth _ _ [] = []
replaceNth n newVal (x : xs) | n == 0    = newVal : xs
                             | otherwise = x : replaceNth (n - 1) newVal xs

iconst :: Int -> Program
iconst i = do
    m@(Machine s _ _) <- get
    put $ m { stack = i : s }

store :: Int -> Program
store i = do
    m@(Machine s r _) <- get
    case s of
        (h : t) -> put $ m { stack = t, registers = replaceNth i h r }
        _       -> undefined

load :: Int -> Program
load i = do
    m@(Machine s r _) <- get
    put $ m { stack = (r !! i) : s }

add :: Program
add = do
    m@(Machine s _ _) <- get
    case s of
        (x : y : t) -> put $ m { stack = (x + y) : t }
        _           -> undefined

sub :: Program
sub = do
    m@(Machine s _ _) <- get
    case s of
        (x : y : t) -> put $ m { stack = (y - x) : t }
        _           -> undefined

eq :: Program
eq = do
    m@(Machine s _ _) <- get
    case s of
        (x : y : t) -> put $ m { stack = (if y == x then 1 else 0) : t }
        _           -> undefined

le :: Program
le = do
    m@(Machine s _ _) <- get
    case s of
        (x : y : t) -> put $ m { stack = (if y <= x then 1 else 0) : t }
        _           -> undefined

pop :: Program
pop = do
    m@(Machine s _ _) <- get
    case s of
        (_ : t) -> put m { stack = t }
        _       -> undefined

branch :: String -> Program -> Program
branch br sf = do
    m@(Machine _ _ b) <- get
    put $ m { branches = (br, sf) : b }
    sf

goto :: String -> Program
goto br = do
    m@(Machine _ _ b) <- get
    case lookup br b of
        Just p -> p
        _      -> undefined

ifnz sf = do
    m@(Machine s _ _) <- get
    case s of
        (i : t) -> put m { stack = t } >> when (i /= 0) sf
        _       -> return ()

fib :: Program
fib = do
    iconst 10
    store 0
    iconst 1
    store 1
    branch "a" $ do
        load 1
        load 2
        add
        load 1
        store 2
        store 1
        load 0
        iconst 1
        sub
        store 0
        load 0
        ifnz $ goto "a"
    load 1

runMachine :: State Machine a -> Int
runMachine p = head . stack $ execState p machine

-- >>> runfib
-- 89
runfib = runMachine fib
