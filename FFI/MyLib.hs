{-# LANGUAGE ForeignFunctionInterface #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- ghc MyLib.hs -o haha lib.cpp -lstdc++

import           Foreign
import           Foreign.C.Types
import           Foreign.Marshal.Array

data MyStruct = MyStruct
    { d :: Double
    , c :: Word8
    , i :: Int32
    }

instance Storable MyStruct where
    alignment _ = 8
    sizeOf _ = 16
    peek ptr =
        MyStruct <$> peekByteOff ptr 0 <*> peekByteOff ptr 8 <*> peekByteOff
            ptr
            12 -- skip padding bytes after "c"
    poke ptr (MyStruct d c i) = do
        pokeByteOff ptr 0  d
        pokeByteOff ptr 8  c
        pokeByteOff ptr 12 i

foreign import ccall "lib.hpp hello"
    hello :: CInt -> IO ()

foreign import ccall "lib.hpp printArr"
    printArr :: Ptr CInt -> CInt -> IO ()

foreign import ccall "lib.hpp resetArray"
    resetArray :: Ptr CInt -> CInt -> IO CInt

foreign import ccall "lib.hpp printStruct"
    printStruct :: Ptr MyStruct -> IO ()

main :: IO ()
main = do
    hello 5
    (arr :: Ptr CInt) <- mallocArray 5
    pokeArray arr [1 .. 5]
    printArr arr 5
    a <- resetArray arr 5
    print a
    print =<< peekArray 5 arr
    let ms = MyStruct 3.14 120 123
    s <- malloc :: IO (Ptr MyStruct)
    poke s ms
    printStruct s
    free s
    free arr
