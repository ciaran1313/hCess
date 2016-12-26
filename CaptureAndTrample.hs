module CaptureAndTrample where

  import qualified Data.Map as Map
  import Data.Maybe
  import Location
  import Game (BoardMap)
  import Piece

  capture :: Location -> BoardMap -> BoardMap
  capture location boardMap = captureToward nextLocation (\ _ -> False) (Just location) $ captureToward previousLocation (if isCapture then isStop else (\ _ -> False)) (Map.lookup location boardMap >>= previousLocation) $ boardMap
    where

      isCapture :: Bool
      isCapture = fromMaybe False (isStop <$> Map.lookup location boardMap

      captureToward :: (Piece -> Maybe Location) -> (Piece -> Bool) -> Maybe Location -> BoardMap -> BoardMap
      captureToward f terminationCondition m_location boardMap
        | isNothing m_location || terminationCondition (fromJust pieceAtLocation) = boardMap
        | otherwise = captureToward f terminationCondition (pieceAtLocation >>= f) $ Map.delete (fromJust m_location) boardMap
        where
          pieceAtLocation :: Maybe Piece
          pieceAtLocation = (>>=)(m_location)(\defloc -> Map.lookup defloc boardMap)
