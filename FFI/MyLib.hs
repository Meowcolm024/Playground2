{-# LANGUAGE ForeignFunctionInterface #-}

-- ghc MyLib.hs -o haha lib.cpp -lstdc++

import Foreign.C.Types

foreign import ccall "lib.hpp hello"
    hello :: CInt -> IO ()

main :: IO ()
main = hello 5
