module Hello where

import Control.Monad (forM_)

main :: IO()
main = forM_ [1..10] $ \x ->
    putStrLn $ "Hello " ++ show x
