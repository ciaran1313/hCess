module Location where

  import RomanNumerals
  import Data.Maybe

  data Location = Location{
    t_value :: Int  ,
    x_value :: Int  ,
    y_value :: Int  }
    deriving (Eq, Ord)

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

  instance Show Location where
    show (Location t x y) = (toFile x) : (toRank y) : (toRomanNumeral t)

  instance Read Location where
    readsPrec d r = [(readLocation r, [])]
      where
        readLocation :: String -> Location
        readLocation(file:rank:turn) = Location t x y
          where
            t, x, y :: Int
            t = fromJust $ fromTurn (turn)
            x = fromJust $ fromFile [file]
            y = fromJust $ fromRank [rank]
