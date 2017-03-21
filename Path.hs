module Path where

  import Data.List (sort)

  import Piece.Core (Kind(..))
  import Location (Location(..))
  import MovementLimitations
  import OffsetLocation (OffsetLocation(..), calculateOffsetLocation)

  calculateDjumpPath :: [Int] -> Location -> Location -> Maybe [Location]
  calculateDjumpPath expectedDiffList startSquare destination
    | actualDiffList == expectedDiffList = Just []
    | otherwise = Nothing
    where
      actualDiffList :: [Int]
      actualDiffList = sort $ map(\f -> abs $ f destination - f startSquare)[t_value, x_value, y_value]

  calculateLinearPathWithOffsetLocation :: OffsetLocation -> [Location]
  calculateLinearPathWithOffsetLocation input
    | distance input <= 1 = []
    | otherwise = nextLocation : calculateLinearPathWithOffsetLocation OffsetLocation {
      t_direction = t_direction input   ,
      x_direction = x_direction input   ,
      y_direction = y_direction input   ,
      distance = distance input - 1     ,
      origin = nextLocation             }
    where
      nextLocation :: Location
      nextLocation = Location new_t new_x new_y
        where
          new_t, new_x, new_y :: Int
          new_t = (+)(t_direction input)(t_value $ origin input)
          new_x = (+)(x_direction input)(x_value $ origin input)
          new_y = (+)(y_direction input)(y_value $ origin input)

  calculateLinearPath :: MovementLimitations -> Location -> Location -> Maybe [Location]
  calculateLinearPath movementLimitations startSquare destination = calculateLinearPathWithOffsetLocation <$> calculateOffsetLocation movementLimitations startSquare destination

  calculatePath :: Bool -> Kind -> Location -> Location -> Maybe [Location]
  calculatePath isCapture@(True ) (Pawn _) = calculateDjumpPath[0,1,1]
  calculatePath isCapture@(False) (Pawn hasMoved@(True)) = calculateDjumpPath[0,0,1]
  calculatePath isCapture@(False) (Pawn hasMoved@(False)) = calculateLinearPath (MovementLimitations{straightPathAllowed=True, diagonalPathAllowed=False, maximumDistance = 2})
  calculatePath _ (Rook _) = calculateLinearPath (MovementLimitations{straightPathAllowed=True, diagonalPathAllowed=False, maximumDistance = maxBound})
  calculatePath _ (Knight) = calculateDjumpPath [0,1,2]
  calculatePath _ (Bishop) = calculateLinearPath (MovementLimitations{straightPathAllowed=True, diagonalPathAllowed=False, maximumDistance = maxBound})
  calculatePath _ (Queen) = calculateLinearPath (MovementLimitations{straightPathAllowed=True, diagonalPathAllowed=True, maximumDistance = maxBound})
  calculatePath _ (King _) = calculateLinearPath (MovementLimitations{straightPathAllowed=True, diagonalPathAllowed=False, maximumDistance = 1})
