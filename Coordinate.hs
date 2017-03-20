module Coordinate where

  import Game.Core (Game, turnNumber)
  import RomanNumerals (romanNumeralChars, toRomanNumeral, fromRomanNumeral)

  data Coordinate = T | X | Y
    deriving (Eq, Show, Read)

  toFile :: Int -> Char
  toFile = toEnum . (+)(97)

  toRank :: Int -> Char
  toRank = toEnum . (+)(49)

  toTurn :: Int -> String
  toTurn = toRomanNumeral

  fromFile :: String -> Maybe Int
  fromFile "a" = Just 0
  fromFile "b" = Just 1
  fromFile "c" = Just 2
  fromFile "d" = Just 3
  fromFile "e" = Just 4
  fromFile "f" = Just 5
  fromFile "g" = Just 6
  fromFile "h" = Just 7
  fromFile  _  = Nothing

  fromRank :: String -> Maybe Int
  fromRank "1" = Just 0
  fromRank "2" = Just 1
  fromRank "3" = Just 2
  fromRank "4" = Just 3
  fromRank "5" = Just 4
  fromRank "6" = Just 5
  fromRank "7" = Just 6
  fromRank "8" = Just 7
  fromRank  _  = Nothing

  fromTurn :: String -> Maybe Int
  fromTurn = fromRomanNumeral

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
  identifyEnumFunctionIn str
    | foldl(\acc c -> elem c romanNumeralChars && acc)(True)(str) = Just T
    | otherwise = Nothing
