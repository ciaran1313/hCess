module HTMLF where

  import Haste
  import Haste.App
  import Haste.DOM
  import Haste.Events

  import CrossSection hiding (vis_t, vis_x, vis_y, grid, game)
  import Coordinate
  import Location
  import Piece
  import Game

  data BoardElem = Square Location Elem | Header Coordinate Int Elem | Divider Elem

  clickable :: BoardElem -> Bool
  clickable (Square _ _) = True
  clickable (Header _ _ _) = True
  clickable _ = False

  getLocation :: BoardElem -> Maybe Location
  getLocation (Square location _) = Just location
  getLocation _ = Nothing

  get_DOM_elem :: BoardElem -> Elem
  get_DOM_elem (Square _ element) = element
  get_DOM_elem (Divider element) = element
  get_DOM_elem (Header _ _ element) = element

  showCrossSection :: MonadIO m => CrossSection -> m [BoardElem]
  showCrossSection (CrossSection (vis_t, n) vis_x vis_y grid game) = foldr(\x acc -> (:) <$> x <*> acc) (return []) boardElements
    where
      boardElements :: MonadIO m => [m BoardElem]
      boardElements = foldl (\acc y -> acc ++ makeRow y ++ horizontalDivider) (columnHeaderRow ++ newLine : horizontalDivider) (enumFromTo 0 $ lastIndexOf vis_y game)
        where

          rowHeaderLength :: Int -> Int
          rowHeaderLength = length . enumFunctionFor vis_y

          indentLength :: Int
          indentLength = (succ . maximum) $ map rowHeaderLength (enumFromTo 0 $ lastIndexOf vis_y game) -- the length of the longest row header plus one

          space :: MonadIO m => Int -> m BoardElem
          space len = Divider <$> newTextElem(replicate len ' ')

          columnHeaderRow :: MonadIO m => [m BoardElem]
          columnHeaderRow = (space $ indentLength + 2) : (foldr (\x acc -> (columnHeader x) : [space $ 4 - columnHeaderLength x] ++ acc) [] (enumFromTo 0 $ lastIndexOf vis_x game))
            where
              columnHeader :: MonadIO m => Int -> m BoardElem
              columnHeader x = do {
                element <- newElem("span");
                setAttr element "class" "header";
                newTextElem (enumFunctionFor vis_x x) >>= appendChild element;
                return $ Header vis_x x element;
              }

              columnHeaderLength :: Int -> Int
              columnHeaderLength = (length . enumFunctionFor vis_x)

          x_length :: Int
          x_length = lastIndexOf vis_x game + 1

          verticalDivider, newLine :: MonadIO m => m BoardElem
          verticalDivider = do {
            element <- newElem("span");
            setProp element "innerHTML" "|";
            setAttr element "class" "background";
            return $ Divider element;
          }
          newLine = Divider <$> newElem("br")

          horizontalDivider :: MonadIO m => [m BoardElem]
          horizontalDivider = (space indentLength) : [dividerBody, newLine]
            where
              dividerBody :: MonadIO m => m BoardElem
              dividerBody = do {
                element <- newElem("span");
                setProp element "innerHTML" (foldr(++) "+" $ replicate x_length "+ - ");
                setAttr element "class" "background";
                return $ Divider element;
              }

          makeRow :: MonadIO m => Int -> [m BoardElem]
          makeRow y = rowHeader : space(indentLength - rowHeaderLength y) : rowBody
            where

              rowHeader :: MonadIO m => m BoardElem
              rowHeader = do {
                element <- newElem("span");
                setAttr element "class" "header";
                newTextElem (enumFunctionFor vis_y y) >>= appendChild element;
                return $ Header vis_y y element;
              }

              square :: MonadIO m => Location -> m BoardElem
              square location = do {
                element <- newElem("span");
                setAttr element "class" "piece";
                setProp element "innerHTML" (htmlSymbol $ getPieceAt location game);
                if Just location == selectedSquare game
                  then setProp element "id" "selected"
                  else return ();
                return $ Square location element;
              }

              rowBody :: MonadIO m => [m BoardElem]
              rowBody = foldr(\x acc -> verticalDivider : square x : acc)[verticalDivider, newLine] $ take x_length (grid!!y)
