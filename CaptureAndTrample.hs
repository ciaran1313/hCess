module CaptureAndTrample where

  import qualified Data.Map as Map
  import Data.Maybe
  import Location
  import Game (BoardMap)
  import Piece

  capture :: Location -> BoardMap -> BoardMap
  capture location boardMap = captureToward nextLocation (Just location) $ captureToward previousLocation (Map.lookup location boardMap >>= previousLocation) $ boardMap
    where
      captureToward :: (Piece -> Maybe Location) -> Maybe Location -> BoardMap -> BoardMap
      captureToward f m_location boardMap
        | isNothing m_location = boardMap
        | otherwise = captureToward f (pieceAtLocation >>= f) $ Map.delete (fromJust m_location) boardMap
        where
          pieceAtLocation :: Maybe Piece
          pieceAtLocation = (>>=)(m_location)(\defloc -> Map.lookup defloc boardMap)
