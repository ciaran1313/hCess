module Location where

  import Data.Maybe (fromMaybe)

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
    readsPrec _ (file:rank:turn) = maybe [] (\location -> [(location, "")]) (Location <$> t <*> x <*> y)
      where
          t, x, y :: Maybe Int
          t = fromTurn (turn)
          x = fromFile [file]
          y = fromRank [rank]

    readsPrec _ _ = []
