module Select where

  import Control.Concurrent
  import Control.Concurrent.MVar

  import Data.Maybe

  import Location
  import qualified Game
  import Piece
  import qualified Status
  import Status (Status)

  select :: Location -> (MVar Game.Game, MVar Status) -> IO ()
  select location (game_MVar, status_MVar) = do {
    game <- readMVar game_MVar;
    (if isNothing (Game.getPieceAt game location)
      then changeStatus (Status.Player_Tried_To_Select_An_Empty_Square location)
      else if (/=)(colour <$> Game.getPieceAt game location)(Just $ Game.turnColour game)
        then changeStatus (Status.Player_Tried_To_Select_An_Opponents_Piece location)
        else if isJust (Game.getPieceAt game location >>= nextLocation)
          then changeStatus (Status.Player_Tried_To_Select_An_Piece_Thats_Already_Been_Moved location $ Game.getPieceAt game location)
          else do {
            swapMVar game_MVar (Game.setSelectedSquare game $ Just location);
            changeStatus Status.No_Issues;
            return ();
          }
    );
  } where
      changeStatus :: Status -> IO ()
      changeStatus newStatus = do {
        swapMVar status_MVar newStatus;
        return ();
      }

  deselect :: MVar Game.Game -> IO ()
  deselect game_MVar = do {
    game <- readMVar game_MVar;
    swapMVar game_MVar (Game.setSelectedSquare game Nothing);
    return ();
  }
