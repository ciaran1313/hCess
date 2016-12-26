module Location where

  import RomanNumerals

  data Location = Location{
    t_value :: Int  ,
    x_value :: Int  ,
    y_value :: Int  }
    deriving (Eq, Ord)

  toFile :: Int -> Char
  toFile n = toEnum(n+97) :: Char

  toRank :: Int -> Char
  toRank n = toEnum(n+49) :: Char

  toTurn :: Int -> String
  toTurn = romanNumeral

  instance Show Location where
    show (Location t x y) = (toFile x) : (toRank y) : (romanNumeral t)
