{-# LANGUAGE ForeignFunctionInterface #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- ghc MyLib.hs -o haha lib.cpp -lstdc++

import Foreign.C.Types
import Foreign.Marshal.Array
import Foreign

foreign import ccall "lib.hpp hello"
    hello :: CInt -> IO ()

foreign import ccall "lib.hpp printArr"
    printArr :: Ptr CInt -> CInt -> IO ()

foreign import ccall "lib.hpp resetArray"
    resetArray :: Ptr CInt -> CInt -> IO CInt

main :: IO ()
main = do 
    hello 5
    (arr :: Ptr CInt) <- mallocArray 5
    pokeArray arr [1..5]
    printArr arr 5
    a <- resetArray arr 5
    print a
    print =<< peekArray 5 arr
