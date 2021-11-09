module Duck where

class (FlyBehavior d, QuarkBehavior d) => DuckBehavior d where
  swim :: d -> String

class FlyBehavior f where
  fly :: f -> String

class QuarkBehavior q where
  quark :: q -> String

data Duck = RubberDuck | GreenDuck deriving (Show ,Eq)

instance FlyBehavior Duck where
    fly RubberDuck = "Can't fly!"
    fly GreenDuck = "Fly low!"

instance QuarkBehavior Duck where
    quark RubberDuck = "Omg!"
    quark GreenDuck = "QUARK!"

instance DuckBehavior Duck where
    swim _ = "swimming"

