module Select where

  import Control.Concurrent.MVar (MVar, readMVar, swapMVar)

  import Data.Maybe (isJust, isNothing)

  import Location (Location)
  import Game.Core (Game(..), getPieceAt)
  import Game.Mutators (setSelectedSquare)
  import Piece.Core (colour, nextLocation)
  import Status (Status(..))

  select :: Location -> (MVar Game, MVar Status) -> IO ()
  select location (game_MVar, status_MVar) = do {
    game <- readMVar game_MVar;
    (if isNothing (getPieceAt game location)
      then changeStatus (Player_Tried_To_Select_An_Empty_Square location)
      else if (/=)(colour <$> getPieceAt game location)(Just $ turnColour game)
        then changeStatus (Player_Tried_To_Select_An_Opponents_Piece location)
        else if isJust (getPieceAt game location >>= nextLocation)
          then changeStatus (Player_Tried_To_Select_An_Piece_Thats_Already_Been_Moved location $ getPieceAt game location)
          else do {
            swapMVar game_MVar (setSelectedSquare game $ Just location);
            changeStatus No_Issues;
            return ();
          }
    );
  } where
      changeStatus :: Status -> IO ()
      changeStatus newStatus = do {
        swapMVar status_MVar newStatus;
        return ();
      }

  deselect :: MVar Game -> IO ()
  deselect game_MVar = do {
    game <- readMVar game_MVar;
    swapMVar game_MVar (setSelectedSquare game Nothing);
    return ();
  }
