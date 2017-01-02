module RomanNumerals where

  import qualified Data.Map as Map

  type RomanNumeral = String

  romanNumberalCharacterValues :: Map.Map Char Int
  romanNumberalCharacterValues = Map.fromList [
    ('n', 0)    ,
    ('i', 1)    ,
    ('v', 5)    ,
    ('x', 10)   ,
    ('l', 50)   ,
    ('c', 100)  ,
    ('d', 500)  ,
    ('m', 1000) ]

  romanNumeralChars :: [Char]
  romanNumeralChars = Map.keys romanNumberalCharacterValues

  toRomanNumeral :: Int -> RomanNumeral
  toRomanNumeral 0 = "n"
  toRomanNumeral x = toRomanNumeral' x
    where
      toRomanNumeral' :: Int -> RomanNumeral
      toRomanNumeral' x
        | x >= 1000 = 'm' : toRomanNumeral' (x - 1000)
        | x >= 0900 = "cm"++toRomanNumeral' (x - 0900)
        | x >= 0500 = 'd' : toRomanNumeral' (x - 0500)
        | x >= 0400 = "cd"++toRomanNumeral' (x - 0400)
        | x >= 0100 = 'c' : toRomanNumeral' (x - 0100)
        | x >= 0090 = "xc"++toRomanNumeral' (x - 0090)
        | x >= 0050 = 'l' : toRomanNumeral' (x - 0050)
        | x >= 0040 = "xl"++toRomanNumeral' (x - 0040)
        | x >= 0010 = 'x' : toRomanNumeral' (x - 0010)
        | x >= 0009 = "ix"++toRomanNumeral' (x - 0009)
        | x >= 0005 = 'v' : toRomanNumeral' (x - 0005)
        | x >= 0004 = "iv"++toRomanNumeral' (x - 0004)
        | x >= 0001 = 'i' : toRomanNumeral' (x - 0001)
        | otherwise = ""

  fromRomanNumeral :: RomanNumeral -> Maybe Int
  fromRomanNumeral = fromRomanNumeral' (Just 0) . map (flip Map.lookup $ romanNumberalCharacterValues)
      where
        fromRomanNumeral' :: Maybe Int -> [Maybe Int] -> Maybe Int
        fromRomanNumeral' n [] = n
        fromRomanNumeral' n (x:xs) = addOrSubtract <$> fromRomanNumeral' n xs <*> x
          where
            addOrSubtract :: Int -> Int -> Int
            addOrSubtract
              | (not . null)(xs) && (<)(x)(head xs) = (-)
              | otherwise = (+)
