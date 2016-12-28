module Coordinate where

  import Game
  import Location

  data Coordinate = T | X | Y
    deriving (Eq, Show, Read)

  thingFor :: a -> a -> a -> Coordinate -> a
  thingFor t x y T = t
  thingFor t x y X = x
  thingFor t x y Y = y

  lastIndexOf :: Coordinate -> Game -> Int
  lastIndexOf T = turnNumber
  lastIndexOf X = \_-> 7
  lastIndexOf Y = \_-> 7

  enumFunctionFor :: Coordinate -> (Int -> String)
  enumFunctionFor T = toTurn
  enumFunctionFor X = (\n -> [toFile n])
  enumFunctionFor Y = (\n -> [toRank n])
