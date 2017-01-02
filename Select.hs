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
          | the_player_has_a_piece_at_the_square_theyre_trying_to_select && the_piece_has_no_next_location = Just location
          | otherwise = Nothing
          where

            the_player_has_a_piece_at_the_square_theyre_trying_to_select :: Bool
            the_player_has_a_piece_at_the_square_theyre_trying_to_select = (==)(colour <$> getPieceAt location game)(Just $ turnColour game)

            the_piece_has_no_next_location :: Bool
            the_piece_has_no_next_location = (==)(getPieceAt location game >>= nextLocation)(Nothing)


  deselect :: Game -> Game
  deselect game = Game {
    turnNumber = turnNumber game        ,
    turnColour = turnColour game        ,
    selectedSquare = Nothing            ,
    boardMap = boardMap game            }
