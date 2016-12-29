module Select where

  import Location
  import Game
  import Piece

  select :: Location -> Game -> Game
  select location game = Game {
      turnNumber = turnNumber game        ,
      turnColour = turnColour game        ,
      selectedSquare = newSelectedSquare  ,
      boardMap = boardMap game            }
      where
        newSelectedSquare :: Maybe Location
        newSelectedSquare
          | fmap colour (getPieceAt location game) /= Just (turnColour game) = Nothing
          | otherwise = Just location

  deselect :: Game -> Game
  deselect game = Game {
    turnNumber = turnNumber game        ,
    turnColour = turnColour game        ,
    selectedSquare = Nothing            ,
    boardMap = boardMap game            }
