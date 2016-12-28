module RomanNumerals where

  type RomanNumeral = String

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

  fromRomanNumeral :: RomanNumeral -> Int
  fromRomanNumeral = fromRomanNumeral' 0 . map valueForChar
      where

        valueForChar :: Char -> Int
        valueForChar 'n' = 0
        valueForChar 'i' = 1
        valueForChar 'v' = 5
        valueForChar 'x' = 10
        valueForChar 'l' = 50
        valueForChar 'c' = 100
        valueForChar 'd' = 500
        valueForChar 'm' = 1000

        fromRomanNumeral' :: Int -> [Int] -> Int
        fromRomanNumeral' n [] = n
        fromRomanNumeral' n (x:xs) = (addOrSubtract)(fromRomanNumeral' n xs)(x)
          where
            addOrSubtract :: Int -> Int -> Int
            addOrSubtract
              | (not . null)(xs) && (<)(x)(head xs) = (-)
              | otherwise = (+)
