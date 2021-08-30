import           Control.Monad                  ( replicateM )
import           System.Random                  ( randomRIO )

nums :: IO [Integer]
nums = replicateM 32768 $ randomRIO (0, 256)

sums :: [Integer] -> Integer
sums xs = sum $ map (const (sum xs)) [1 .. 100000]

main :: IO ()
main = print . sums =<< nums
