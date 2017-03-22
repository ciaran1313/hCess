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
    readsPrec d r = [(readLocation r, [])]
      where

        no_parse = errorWithoutStackTrace "Prelude.read: no parse"

        readLocation :: String -> Location
        readLocation(file:rank:turn) = Location t x y
          where
            t, x, y :: Int
            t = fromMaybe no_parse $ fromTurn (turn)
            x = fromMaybe no_parse $ fromFile [file]
            y = fromMaybe no_parse $ fromRank [rank]

        readLocation _ = no_parse
