module RelativePosition where

  import Data.Maybe
  import Location
  import MovementLimitations

  type Direction = Int

  data RelativePosition = RelativePosition {
    t_direction   ::  Direction  ,
    x_direction   ::  Direction  ,
    y_direction   ::  Direction  ,
    distance      ::  Int        ,
    origin        ::  Location   }

  toRelativePosition :: MovementLimitations -> Location -> Location -> Maybe RelativePosition
  toRelativePosition (MovementLimitations straightPathAllowed diagonalPathAllowed max_distance) startSquare destination
    | (fromMaybe False $ (>) <$> calculate_distance <*> max_distance) = Nothing
    | not $ (straightPathAllowed && changeCount == 1) || (diagonalPathAllowed && changeCount == 2) = Nothing
    | startSquare == destination = Just $ RelativePosition {
      t_direction = 0           ,
      x_direction = 0           ,
      y_direction = 0           ,
      distance    = 0           ,
      origin      = startSquare }
    | otherwise = RelativePosition <$> calculate_t <*> calculate_x <*> calculate_y <*> calculate_distance <*> Just startSquare
    where

      changes :: [Int]
      changes = map(\f -> f destination - f startSquare)[t_value, x_value, y_value]

      processedChanges :: [Int]
      processedChanges = map abs $ filter (/=0) changes

      changeCount :: Int
      changeCount = length processedChanges

      calculateCoordinateValue :: Int -> Maybe Direction
      calculateCoordinateValue index
        | changes!!index > 0 =  Just(0+1)
        | changes!!index < 0 =  Just(0-1)
        | otherwise          =  Just(000)

      calculate_t :: Maybe Direction
      calculate_t = calculateCoordinateValue 0

      calculate_x :: Maybe Direction
      calculate_x = calculateCoordinateValue 1

      calculate_y :: Maybe Direction
      calculate_y = calculateCoordinateValue 2

      calculate_distance :: Maybe Int
      calculate_distance = foldl(\acc x -> if Just x == acc then acc else Nothing) (Just $ head processedChanges) (processedChanges)
