import qualified Data.Map                      as Map

type Date = String
type Code = String
type CovidData = Map.Map Date PackedData
type RegionList = Map.Map Code Region
type Viewer = (Code, Date, PackedData -> Integer)

data PackedData = PackedData
    { cases   :: Integer
    , deaths  :: Integer
    , vaccine :: Integer
    }
    deriving Show

data Region = Region
    { name      :: String
    , code      :: Code
    , covidData :: CovidData
    }
    deriving Show

getCovidData :: RegionList -> Viewer -> Maybe Integer
getCovidData rl (c, d, f) =
    f <$> (Map.lookup c rl >>= Map.lookup d . covidData)


qsort :: Ord a => [a] -> [a]
qsort []       = []
qsort (x : xs) = qsort (filter (< x) xs) ++ [x] ++ qsort (filter (>= x) xs)

merge :: Ord a => [a] -> [a] -> [a]
merge xs [] = xs
merge [] ys = ys
merge (x : xs) (y : ys) =
    if x < y then x : merge xs (y : ys) else y : merge (x : xs) ys

msort :: Ord a => [a] -> [a]
msort []  = []
msort [x] = [x]
msort xs =
    let (l, r) = splitAt (length xs `div` 2) xs in merge (msort l) (msort r)
