module Location where

  import RomanNumerals

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

  fromFile :: Char -> Int
  fromFile = (+)(-97) . fromEnum

  fromRank :: Char -> Int
  fromRank = (+)(-49) . fromEnum

  fromTurn :: String -> Int
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
            t = fromTurn turn
            x = fromFile file
            y = fromRank rank
