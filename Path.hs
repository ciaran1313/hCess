module Path where

  import Data.List (sort)

  import qualified Piece
  import Location
  import MovementLimitations
  import OffsetLocation

  calculateDjumpPath :: [Int] -> Location -> Location -> Maybe [Location]
  calculateDjumpPath expectedDiffList startSquare destination
    | actualDiffList == expectedDiffList = Just []
    | otherwise = Nothing
    where
      actualDiffList :: [Int]
      actualDiffList = sort $ map(\f -> abs $ f destination - f startSquare)[t_value, x_value, y_value]

  calculateLinearPath :: MovementLimitations -> Location -> Location -> Maybe [Location]
  calculateLinearPath movementLimitations startSquare destination = f <$> calculateOffsetLocation movementLimitations startSquare destination
    where
      f :: OffsetLocation -> [Location]
      f r
        | distance r == 0 = []
        | otherwise = nextLocation : f OffsetLocation {
          t_direction = t_direction r   ,
          x_direction = x_direction r   ,
          y_direction = y_direction r   ,
          distance = distance r - 1     ,
          origin = nextLocation         }
        where
          nextLocation :: Location
          nextLocation = Location new_t new_x new_y
            where
              new_t, new_x, new_y :: Int
              new_t = (+)(t_direction r)(t_value $ origin r)
              new_x = (+)(x_direction r)(x_value $ origin r)
              new_y = (+)(y_direction r)(y_value $ origin r)

  calculatePath :: Bool -> Piece.Kind -> Location -> Location -> Maybe [Location]
  calculatePath isCapture@(True ) (Piece.Pawn _) = calculateDjumpPath[0,1,1]
  calculatePath isCapture@(False) (Piece.Pawn hasMoved@(True)) = calculateDjumpPath[0,0,1]
  calculatePath isCapture@(False) (Piece.Pawn hasMoved@(False)) = calculateLinearPath (MovementLimitations{straightPathAllowed=True, diagonalPathAllowed=False, maximumDistance = 2})
  calculatePath _ (Piece.Rook _) = calculateLinearPath (MovementLimitations{straightPathAllowed=True, diagonalPathAllowed=False, maximumDistance = maxBound})
  calculatePath _ (Piece.Knight) = calculateDjumpPath [0,1,2]
  calculatePath _ (Piece.Bishop) = calculateLinearPath (MovementLimitations{straightPathAllowed=True, diagonalPathAllowed=False, maximumDistance = maxBound})
  calculatePath _ (Piece.Queen) = calculateLinearPath (MovementLimitations{straightPathAllowed=True, diagonalPathAllowed=True, maximumDistance = maxBound})
  calculatePath _ (Piece.King _) = calculateLinearPath (MovementLimitations{straightPathAllowed=True, diagonalPathAllowed=False, maximumDistance = 1})
