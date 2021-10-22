import qualified Data.Map                      as Map

type Date = String
type Code = String
type CovidData = Map.Map Date PackedData
type RegionList = Map.Map Code Region
type Viewer = (Code, Date, PackedData -> Integer)

data PackedData = PackedData
    { cases     :: Integer
    , casesPM   :: Integer
    , deaths    :: Integer
    , deathsPM  :: Integer
    , vaccine   :: Integer
    , vaccinePM :: Integer
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
