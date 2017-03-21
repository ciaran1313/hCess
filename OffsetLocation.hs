module OffsetLocation where

  import Location (Location, t_value, x_value, y_value)
  import MovementLimitations (MovementLimitations(..))

  type Direction = Int

  data OffsetLocation = OffsetLocation {
    t_direction   ::  Direction  ,
    x_direction   ::  Direction  ,
    y_direction   ::  Direction  ,
    distance      ::  Int        ,
    origin        ::  Location   }
    deriving (Show)

  calculateOffsetLocation :: MovementLimitations -> Location -> Location -> Maybe OffsetLocation
  calculateOffsetLocation (MovementLimitations straightPathAllowed diagonalPathAllowed maximumDistance) startSquare destination
    | (calculate_distance > maximumDistance) = Nothing -- if you try to move the piece further than it's allowed, it will return Nothing
    | not $ (||)(straightPathAllowed && changeCount == 1)(diagonalPathAllowed && changeCount == 2) = Nothing -- if the it's not moving in a direction it's allowed to, it will return Nothing
    | otherwise = Just $ OffsetLocation calculate_t calculate_x calculate_y calculate_distance startSquare
    where

      changes, processed_changes :: [Int]
      changes = map(\f -> f destination - f startSquare)[t_value, x_value, y_value]
      processed_changes = map abs $ filter (/=0) changes -- filters out all the directions that dont change in value, and gets the absolute value of them

      changeCount :: Int
      changeCount = length processed_changes

      calculateCoordinateValue :: Int -> Direction
      calculateCoordinateValue changeNumber = signum (changes !! changeNumber)

      calculate_t, calculate_x, calculate_y :: Direction
      calculate_t = calculateCoordinateValue 0
      calculate_x = calculateCoordinateValue 1
      calculate_y = calculateCoordinateValue 2

      calculate_distance :: Int
      calculate_distance = maximum $ map abs changes
