module Coordinate where

  import Game
  import Location
  import RomanNumerals (romanNumeralChars)

  data Coordinate = T | X | Y
    deriving (Eq, Show, Read)

  thingFor :: a -> a -> a -> Coordinate -> a
  thingFor t x y T = t
  thingFor t x y X = x
  thingFor t x y Y = y

  lastIndexOf :: Coordinate -> (Game -> Int)
  lastIndexOf T = turnNumber
  lastIndexOf X = (\ _ -> 7)
  lastIndexOf Y = (\ _ -> 7)

  enumFunctionFor :: Coordinate -> (Int -> String)
  enumFunctionFor T = toTurn
  enumFunctionFor X = (\n -> [toFile n])
  enumFunctionFor Y = (\n -> [toRank n])

  deEnumFunctionFor :: Coordinate -> (String -> Maybe Int)
  deEnumFunctionFor T = fromTurn
  deEnumFunctionFor X = fromFile
  deEnumFunctionFor Y = fromRank

  identifyEnumFunctionIn :: String -> Maybe Coordinate
  identifyEnumFunctionIn "" = Nothing
  identifyEnumFunctionIn [c]
    | c `elem` ['a'..'h'] = Just X
    | c `elem` ['1'..'8'] = Just Y
    | c `elem` romanNumeralChars = Just T
    | otherwise = Nothing
  identifyEnumFunction str
    | foldl(\acc c -> elem c romanNumeralChars && acc)(True)(str) = Just T
    | otherwise = Nothing
