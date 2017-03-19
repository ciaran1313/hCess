module Move where

  import Control.Concurrent
  import Control.Concurrent.MVar

  import Data.Maybe
  import qualified Data.Map as Map

  import qualified Game
  import qualified Piece
  import qualified Path
  import qualified Location
  import qualified MovementLimitations
  import qualified Aging
  import qualified CaptureOrTrample
  import qualified Status

  move :: Location.Location -> (MVar Game.Game, MVar Status.Status) -> IO ()
  move destination (game_MVar, status_MVar) = do {
      game <- readMVar game_MVar;
      (if Game.selectedSquare game == Nothing
        then changeStatus Status.Player_Tried_To_Move_With_Nothing_Selected
        else if (==)(Just $ Game.turnColour game)(Piece.colour <$> Game.getPieceAt game destination)
          then changeStatus Status.Player_Tried_To_Capture_Their_Own_Piece
          else if path game == Nothing
            then changeStatus Status.Illegal_Path
            else if pathIsObstructed game
              then changeStatus (Status.Obstructed_Path_At $ obstructions game)
              else do {
                changeStatus Status.No_Issues;

                return ();
              }
      );
    } where
      {-}
        markPath :: [Location.Location] -> Location.Location -> IO ()
        markPath (location:nextLocation:locations) previousLocation = do {
          game <- takeMVar game_MVar;
          Game.putPieceAt game location (fromJust $ getPieceAt game location);
          return ();
        -}

        path :: Game.Game -> Maybe [Location.Location]
        path game = (Path.calculatePath isCapture <$> kind <*> Game.selectedSquare game <*> Just destination) >>= id
          where

            isCapture :: Bool
            isCapture = isJust $ Game.getPieceAt game destination

            kind :: Maybe Piece.Kind
            kind = fmap Piece.kind (Game.selectedSquare game >>= Game.getPieceAt game)

        obstructions :: Game.Game -> [Location.Location]
        obstructions game = fromMaybe [] $ filter (isJust . Game.getPieceAt game) <$> (path game)

        pathIsObstructed :: Game.Game -> Bool
        pathIsObstructed game = (length $ obstructions game) > 0

        changeStatus :: Status.Status -> IO ()
        changeStatus newStatus = do {
          swapMVar status_MVar newStatus;
          return ();
        }
