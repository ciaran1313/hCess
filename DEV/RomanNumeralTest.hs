import RomanNumerals

listRomanNumerals :: [(Bool, (Int, RomanNumeral, Int))]
listRomanNumerals = map(\x -> ((x == (fromRomanNumeral $ toRomanNumeral x), (x, toRomanNumeral x, fromRomanNumeral $ toRomanNumeral x))))[0..]

hasErrorBefore n = elem(False)(map fst $ take n listRomanNumerals)
