module CrossSection where

  import Game
  import qualified Piece
  import Location
  import Coordinate

  data CrossSection = CrossSection {
    vis_t :: (Coordinate, Int)  ,
    vis_x :: Coordinate         ,
    vis_y :: Coordinate         ,
    grid  :: [[Location]]       ,
    game  :: Game               }

  cutCrossSection :: (Coordinate, Int) -> Coordinate -> Coordinate -> (Game -> CrossSection)
  cutCrossSection (vis_t, n) vis_x vis_y = CrossSection (vis_t, n) vis_x vis_y $ map row [0..]
    where
      row :: Int -> [Location]
      row y = map(\x -> square x y) [0..]
        where
          square :: Int -> Int -> Location
          square x y = Location (thingFor n x y vis_t) (thingFor n x y vis_x) (thingFor n x y vis_y)

  instance Show CrossSection where
    show (CrossSection (vis_t, n) vis_x vis_y grid game) = (++)(cornerHeightIndicator ++ drop (length cornerHeightIndicator) (replicate indentLength ' ' ++ "  " ++ columnHeaderRow)) $ foldl(\acc rowNumber -> acc ++ showRowByNumber rowNumber ++ "\n" ++ divider) divider $ enumFromTo 0 $ lastIndexOf vis_y game
      where

        setStringSize :: Int -> String -> String
        setStringSize size string
          | length string > size = take(size-1) string ++ "~"
          | otherwise = take size $ string ++ repeat ' '

        cornerHeightIndicator :: String
        cornerHeightIndicator = (enumFunctionFor vis_t) n

        columnHeaderRow :: String
        columnHeaderRow = foldr(\x acc -> (setStringSize 4 $ enumFunctionFor vis_x x) ++ acc) "\n" $ enumFromTo 0 $ lastIndexOf vis_x game

        rowHeaders :: [String]
        rowHeaders =  map(enumFunctionFor vis_y) $ enumFromTo 0 $ lastIndexOf vis_y game

        indentLength :: Int
        indentLength = (+) 1 $ foldl(\acc x -> max acc $ length x) 0 rowHeaders

        divider :: String
        divider = (++)(replicate indentLength ' ')(foldr(++) "+\n" $ replicate (lastIndexOf vis_x game + 1) "+ - ")

        showRowByNumber :: Int -> String
        showRowByNumber rowNumber = header ++ rowBody
          where

            header :: String
            header = setStringSize indentLength (rowHeaders!!rowNumber)

            rowBody :: String
            rowBody = foldl(\acc square -> acc ++ show_square square ++ "|") "|" $ take (lastIndexOf vis_x game + 1) $ grid!!rowNumber
              where

                show_square :: Location -> String
                show_square square = Piece.symbol $ getPieceAt square game
