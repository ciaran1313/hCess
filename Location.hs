module Location where

  import Data.Maybe (fromJust)

  import RomanNumerals (toRomanNumeral)
  import {-# SOURCE #-} Coordinate (toFile, toRank, fromTurn, fromFile, fromRank)

  data Location = Location{
    t_value :: Int  ,
    x_value :: Int  ,
    y_value :: Int  }
    deriving (Eq, Ord)

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
