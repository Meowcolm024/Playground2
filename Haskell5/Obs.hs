-- module Obs where
import           Control.Concurrent
import           Control.Monad                  ( forM_ )

mvr :: IO ()
mvr = do
    v <- newMVar 2
    forkIO $ do
        putStrLn "start"
        x <- takeMVar v
        print x
        putMVar v 9
    putStrLn "main"
    threadDelay 500000
    x <- takeMVar v
    print x

chn :: IO ()
chn = do
    c <- newChan
    forkIO $ forM_ [1 .. 8] $ \i -> do
        writeChan c (i * i)
        threadDelay 500000
    putStrLn "Haha"
    threadDelay 1000000
    forM_ [1 .. 8] $ \i -> do
        r <- readChan c
        putStrLn $ "Read: " ++ show r

main :: IO ()
main = do
    mvr
    threadDelay 1000000
    chn