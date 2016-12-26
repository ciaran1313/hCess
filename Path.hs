module Path where

  import qualified Data.Map as Map
  import Data.Maybe
  import RelativePosition
  import Location
  import qualified Piece
  import Game (BoardMap)
  import MovementLimitations
  import Data.List (sort)

  markDjumpPath :: [Int] -> Maybe Piece.Piece -> Location -> Location -> BoardMap -> Maybe BoardMap
  markDjumpPath expectedDiffList piece startSquare destination boardMap
    | actualDiffList == expectedDiffList = (Map.insert startSquare <$> pieceAtStartSquare) <*> (Map.insert destination <$> pieceAtDestination <*> Just boardMap)
    | otherwise = Nothing
    where

      actualDiffList :: [Int]
      actualDiffList = sort $ map(\f -> abs $ f destination - f startSquare)[t_value, x_value, y_value]

      basePiece :: Maybe (Maybe Location -> Maybe Location -> Piece.Piece)
      basePiece = Piece.Piece <$> (Piece.colour <$> piece) <*> (Piece.kind <$> piece) <*> (Just True)

      pieceAtStartSquare :: Maybe Piece.Piece
      pieceAtStartSquare = basePiece <*> (Just $ Just destination) <*> (Piece.previousLocation <$> piece)

      pieceAtDestination :: Maybe Piece.Piece
      pieceAtDestination = basePiece <*> (Just Nothing) <*> (Just $ Just startSquare)


  markLinearPath :: MovementLimitations -> Maybe Piece.Piece -> Location -> Location -> BoardMap -> Maybe BoardMap
  markLinearPath limitations movingPiece startSquare destination boardMap
    | obstructedPath = Nothing
    | otherwise = Map.insert startSquare <$> newPieceAtStartSquare <*> (putMarks <$> originColour <*> originKind <*> (Just $ Just startSquare) <*> calculatedPath <*> Just boardMap)
    where

      newPieceAtStartSquare :: Maybe Piece.Piece
      newPieceAtStartSquare = Piece.Piece <$> (Piece.colour <$> oldPieceAtStartSquare) <*> (Piece.kind <$> oldPieceAtStartSquare) <*> (Just True) <*> Just (head <$> calculatedPath) <*> (Piece.previousLocation <$> oldPieceAtStartSquare)
          where
            oldPieceAtStartSquare :: Maybe Piece.Piece
            oldPieceAtStartSquare = Map.lookup startSquare boardMap

      obstructedPath :: Bool
      obstructedPath = fromMaybe True $ (foldl(\acc x -> if isJust $ Map.lookup x boardMap then True else acc) False) <$> calculatedPath

      originColour :: Maybe Piece.Colour
      originColour = Piece.colour <$> movingPiece

      originKind :: Maybe Piece.Kind
      originKind = Piece.kind <$> movingPiece

      calculatedPath :: Maybe [Location]
      calculatedPath = calculatePath <$> toRelativePosition limitations startSquare destination
        where

          calculatePath :: RelativePosition -> [Location]
          calculatePath r
            | distance r == 0 = []
            | otherwise = nextLocation : calculatePath RelativePosition {
              t_direction = t_direction r   ,
              x_direction = x_direction r   ,
              y_direction = y_direction r   ,
              distance = distance r - 1     ,
              origin = nextLocation         }
            where
              nextLocation :: Location
              nextLocation = Location new_t new_x new_y
                where

                  new_t :: Int
                  new_t = (+)(t_direction r)(t_value $ origin r)

                  new_x :: Int
                  new_x = (+)(x_direction r)(x_value $ origin r)

                  new_y :: Int
                  new_y = (+)(y_direction r)(y_value $ origin r)

      putMarks :: Piece.Colour -> Piece.Kind -> Maybe Location -> [Location] -> BoardMap -> BoardMap
      putMarks _ _ _ [] boardMap = boardMap
      putMarks c k prev (location : locations) boardMap = putMarks c k (Just location) locations newBoardMap
        where
          newBoardMap :: BoardMap
          newBoardMap = Map.insert location piece boardMap
            where
              piece :: Piece.Piece
              piece = Piece.Piece {
                Piece.colour = c                          ,
                Piece.kind = k                            ,
                Piece.isStop = False                      ,
                Piece.nextLocation = next                 ,
                Piece.previousLocation = prev             }
                where
                  next :: Maybe Location
                  next
                    | length locations == 0 = Nothing
                    | otherwise = Just $ head locations
