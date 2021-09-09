import           Control.Monad                  ( replicateM )
import           System.Random                  ( randomRIO )

nums :: IO [Integer]
nums = replicateM 32768 $ randomRIO (0, 256)

sums :: [Integer] -> Integer
sums xs = sum $ map (const (sum xs)) [1 .. 100000]

main :: IO ()
main = print . sums =<< nums

if' :: Bool -> p -> p -> p
if' True  a _ = a
if' False _ p = p

while :: Monad m => m Bool -> m a -> m ()
while p e = do
    x <- p
    if x then e >> while p e else return ()
