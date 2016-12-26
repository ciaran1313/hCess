module RomanNumerals where

  type RomanNumeral = String

  romanNumeral :: Int -> RomanNumeral
  romanNumeral 0 = "n"
  romanNumeral x = f x
    where
      f :: Int -> RomanNumeral
      f x
        | x >= 1000 = 'm' : f (x - 1000)
        | x >= 0900 = "cm"++f (x - 0900)
        | x >= 0500 = 'd' : f (x - 0500)
        | x >= 0400 = "cd"++f (x - 0400)
        | x >= 0100 = 'c' : f (x - 0100)
        | x >= 0090 = "xc"++f (x - 0090)
        | x >= 0050 = 'l' : f (x - 0050)
        | x >= 0040 = "xl"++f (x - 0040)
        | x >= 0010 = 'x' : f (x - 0010)
        | x >= 0009 = "ix"++f (x - 0009)
        | x >= 0005 = 'v' : f (x - 0005)
        | x >= 0004 = "iv"++f (x - 0004)
        | x >= 0001 = 'i' : f (x - 0001)
        | otherwise = ""
