module Status where

  import Piece (Piece(..))
  import Location (Location)

  data Status = No_Issues
              | Player_Tried_To_Select_An_Empty_Square Location
              | Player_Tried_To_Select_An_Opponents_Piece Location
              | Player_Tried_To_Select_An_Piece_Thats_Already_Been_Moved Location (Maybe Piece)
              | Player_Tried_To_Move_With_Nothing_Selected
              | Player_Tried_To_Capture_Their_Own_Piece
              | Illegal_Path
              | Obstructed_Path_At [Location]
              deriving (Eq)

  message :: Status -> String
  message No_Issues = "No Issues";
  message (Player_Tried_To_Select_An_Empty_Square location) = "The square at " ++ show location ++ " is not occupied, and therefore may not be selected."
  message (Player_Tried_To_Select_An_Opponents_Piece location) = "The square at " ++ show location ++ " is occupied by your opponent, and therefore may not be selected by you."
  message (Player_Tried_To_Select_An_Piece_Thats_Already_Been_Moved location (Just (Piece _ kind _ (Just nextLocation) _))) = "Your " ++ show kind ++ " at " ++ show location ++ " is already moving to " ++ show nextLocation ++ " next turn. Therefore you may not move it."
  message (Player_Tried_To_Select_An_Piece_Thats_Already_Been_Moved location (Just (Piece colour kind _ Nothing _ ))) = "THERE'S A BUG IN THE CODE! Apparently the "  ++ show colour ++ " " ++ show kind ++ " at " ++ show location ++ " is already moving somewhere next turn, however the piece is actually shown to have no next location."
  message (Player_Tried_To_Select_An_Piece_Thats_Already_Been_Moved location Nothing) = "THERE'S A BUG IN THE CODE! Apparently the piece at " ++ show location ++ " has already been moved, but there doesn't appear to be any piece at " ++ show location ++ ". Nevertheless, since there's no piece there, you shouldnt be allowed to select it anyway, but just thought I'd point out the bug."
  message Player_Tried_To_Move_With_Nothing_Selected = "You must select a square in order to move from it."
  message Player_Tried_To_Capture_Their_Own_Piece = "You cannot capture your own pieces."
  message Illegal_Path = "That piece does not move in that shape."
  message (Obstructed_Path_At locations) = "The path is obstructed at " ++ show locations ++ "."
