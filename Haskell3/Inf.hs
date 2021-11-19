{-# LANGUAGE RankNTypes #-}

omg :: forall a. Show a => a -> Int -> IO ()
omg _ 0 = return ()
omg t i = print t >> omg (t, t) (i-1)
