module OOP where
import           Data.Function
import           Data.IORef

class FieldX c where
    _x :: c -> IORef Int
class FieldY c where
    _y :: c -> IORef Int
class MthSet c where
    set :: c -> Int -> IO ()
class MthGet c where
    get :: c -> IO Int
class MthInc c where
    inc :: c -> IO ()
class MthAcc c where
    access :: c -> IO Int

newtype CounterRep = CounterRep {_cx :: IORef Int}

data InstrCounterRep = InstrRep
    { _ix :: IORef Int
    , _iy :: IORef Int
    }

data SetCounter = SetCounter
    { getc :: IO Int
    , setc :: Int -> IO ()
    , incc :: IO ()
    }

data InstrCounter = InstrCounter
    { geti    :: IO Int
    , seti    :: Int -> IO ()
    , inci    :: IO ()
    , accessi :: IO Int
    }

instance FieldX CounterRep where
    _x = _cx
instance FieldX InstrCounterRep where
    _x = _ix
instance FieldY InstrCounterRep where
    _y = _iy
instance MthSet SetCounter where
    set = setc
instance MthGet SetCounter where
    get = getc
instance MthInc SetCounter where
    inc = incc
instance MthSet InstrCounter where
    set = seti
instance MthGet InstrCounter where
    get = geti
instance MthInc InstrCounter where
    inc = inci
instance MthAcc InstrCounter where
    access = accessi

setCounterClass :: (FieldX c1, MthGet c2, MthSet c2) => c1 -> c2 -> SetCounter
setCounterClass r this = SetCounter
    { getc = readIORef (_x r)
    , setc = writeIORef (_x r)
    , incc = do
                 i <- get this
                 set this (i + 1)
    }

newSetCounter :: IO SetCounter
newSetCounter = do
    x <- newIORef 1
    return $ fix (setCounterClass (CounterRep x))

instrCounterClass
    :: (FieldY c1, FieldX c1, MthGet c2, MthSet c2) => c1 -> c2 -> InstrCounter
instrCounterClass r this =
    let super = setCounterClass r this
    in  InstrCounter
            { geti    = get super
            , seti    = \i -> do
                            j <- readIORef (_y r)
                            writeIORef (_y r) (j + 1)
                            set super i
            , inci    = inc super
            , accessi = readIORef (_y r)
            }

newInstrCounter :: IO InstrCounter
newInstrCounter = do
    x <- newIORef 1
    y <- newIORef 0
    return $ fix (instrCounterClass (InstrRep x y))

test :: IO ()
test = do
    c <- newInstrCounter
    d <- newSetCounter
    print =<< get c
    inc c
    inc d
    print =<< get c
    set c 20
    set c 22
    print =<< access c
    print =<< get c
    print =<< get d

setCounterClass' :: CounterRep -> SetCounter -> SetCounter
setCounterClass' r this = SetCounter
    { getc = readIORef (_cx r)
    , setc = writeIORef (_cx r)
    , incc = do
                 i <- get this
                 set this (i + 1)
    }