module Move where

  import Control.Concurrent.MVar (MVar, readMVar, swapMVar)

  import Data.Maybe (isJust, fromMaybe)

  import Game (Game, turnColour, selectedSquare, getPieceAt)
  import Piece (Kind, colour, kind)
  import Path (calculatePath)
  import Location (Location)
  import Status (Status(..))

  move :: Location -> (MVar Game, MVar Status) -> IO ()
  move destination (game_MVar, status_MVar) = do {
      game <- readMVar game_MVar;
      (if selectedSquare game == Nothing
        then changeStatus Player_Tried_To_Move_With_Nothing_Selected
        else if (==)(Just $ turnColour game)(colour <$> getPieceAt game destination)
          then changeStatus Player_Tried_To_Capture_Their_Own_Piece
          else if path game == Nothing
            then changeStatus Illegal_Path
            else if pathIsObstructed game
              then changeStatus (Obstructed_Path_At $ obstructions game)
              else do {
                changeStatus No_Issues;

                return ();
              }
      );
    } where
      {-}
        markPath :: [Location] -> Location -> IO ()
        markPath (location:nextLocation:locations) previousLocation = do {
          game <- takeMVar game_MVar;
          putPieceAt game location (fromJust $ getPieceAt game location);
          return ();
        -}

        path :: Game -> Maybe [Location]
        path game = (calculatePath isCapture <$> piece_kind <*> selectedSquare game <*> Just destination) >>= id
          where

            isCapture :: Bool
            isCapture = isJust $ getPieceAt game destination

            piece_kind :: Maybe Kind
            piece_kind = fmap kind (selectedSquare game >>= getPieceAt game)

        obstructions :: Game -> [Location]
        obstructions game = fromMaybe [] $ filter (isJust . getPieceAt game) <$> (path game)

        pathIsObstructed :: Game -> Bool
        pathIsObstructed game = (length $ obstructions game) > 0

        changeStatus :: Status -> IO ()
        changeStatus newStatus = do {
          swapMVar status_MVar newStatus;
          return ();
        }
