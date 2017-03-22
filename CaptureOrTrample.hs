module CaptureOrTrample where

  import Control.Concurrent.MVar (MVar, readMVar)

  import Game.Core(Game, removePieceAt, associatedLocation)
  import Piece.Core(nextLocation, previousLocation)
  import Location(Location)
  import GeneralFunctions (applyToMVar)

  import Data.Maybe(fromMaybe)

  captureOrTrample :: Location -> MVar Game -> IO ()
  captureOrTrample location game_MVar = do {
      game <- readMVar game_MVar;
      fromMaybe (return ())(captureOrTrample <$> associatedLocation nextLocation location game);
      fromMaybe (return ())(captureOrTrample <$> associatedLocation previousLocation location game);
      applyToMVar game_MVar $ flip removePieceAt location;
      return ();
  }



{-}
  import qualified Data.Map as Map
  import Data.Maybe
  import Location
  import Game (BoardMap, associatedLocation)
  import Piece



  captureOrTrample :: Location -> BoardMap -> BoardMap
  captureOrTrample location boardMap = (captureToward nextLocation never (Just location) . captureToward previousLocation (if isCapture then never else isStop) (associatedLocation previousLocation location boardMap)) boardMap
    where

      isCapture :: Bool
      isCapture = fromMaybe False (isStop <$> Map.lookup location boardMap)

      captureToward :: (Piece -> Maybe Location) -> (Piece -> Bool) -> Maybe Location -> BoardMap -> BoardMap
      captureToward f terminationCondition maybe_location boardMap
        | fromMaybe True $ terminationCondition <$> pieceAtLocation = boardMap -- if the piece fits the termination condition, or there is no piece
        | otherwise = captureToward f terminationCondition (pieceAtLocation >>= f) $ Map.delete (fromJust maybe_location) boardMap
        where
          pieceAtLocation :: Maybe Piece
          pieceAtLocation = maybe_location >>= flip Map.lookup boardMap

      never :: a -> Bool
      never = (\_ -> False)


      -}
