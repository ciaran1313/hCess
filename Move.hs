module Move where

  import Control.Concurrent.MVar (MVar, newMVar, takeMVar, putMVar, readMVar, swapMVar)
  import Control.Monad (replicateM_)

  import Data.Maybe (isJust, fromJust, fromMaybe)

  import GeneralFunctions (applyToMVar)

  import Game.Core (Game, turnColour, selectedSquare, getPieceAt, getSelectedPiece, putPieceAt)
  import Piece.Core (Piece(..), Kind, Colour, colour, kind)
  import Piece.Mutators (setIsStop, setNextLocation, setPreviousLocation)
  import Path (calculatePath)
  import Location (Location)
  import Status (Status(..))
  import Select (deselect)
  import Aging (age)

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
                extendedPath <- return $ (fromJust $ selectedSquare game) : (fromJust $ path game) ++ [destination];
                --replaces the first piece
                piece <- return $ fromJust $ getSelectedPiece game;
                piece <- return $ setNextLocation piece (Just $ extendedPath !! 1);
                applyToMVar game_MVar $ (\g -> putPieceAt g (extendedPath !! 0) piece);
                --places the pieces in the path
                counter <- newMVar (1 :: Int);
                piece <- return $ setIsStop piece False;
                replicateM_ (length extendedPath - 2) $ do {
                  i <- readMVar counter;
                  piece <- return $ setNextLocation piece (Just $ extendedPath !! succ i);
                  piece <- return $ setPreviousLocation piece (Just $ extendedPath !! pred i);
                  applyToMVar game_MVar $ (\g -> putPieceAt g (extendedPath !! i) piece);
                  applyToMVar counter succ;
                  return ();
                };
                --places the final location of the piece
                i <- readMVar counter;
                piece <- return $ setIsStop piece True;
                piece <- return $ setNextLocation piece Nothing;
                piece <- return $ setPreviousLocation piece $ Just (extendedPath !! pred i);
                applyToMVar game_MVar $ (\g -> putPieceAt g (extendedPath !! i) piece);
                --prepares for other player
                applyToMVar game_MVar age;
                --fin
                return ();
              }
      );
    } where

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
