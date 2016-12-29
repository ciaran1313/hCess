module Move where

  import Data.Maybe
  import qualified Data.Map as Map
  import Game hiding (turnNumber, turnColour, selectedSquare, boardMap)
  import qualified Piece
  import Path
  import Location
  import MovementLimitations
  import Aging
  import CaptureOrTrample

  pathFunctionFor :: Piece.Kind -> (Maybe Piece.Piece -> Location -> Location -> BoardMap -> Maybe BoardMap)

  pathFunctionFor (Piece.Pawn hasMoved) = markLinearPath $ MovementLimitations {
    straightPathAllowed = True                                ,
    diagonalPathAllowed = False                               ,
    maximumDistance     = Just (if hasMoved then 1 else 2)    }

  pathFunctionFor (Piece.Rook _) = markLinearPath $ MovementLimitations {
    straightPathAllowed = True    ,
    diagonalPathAllowed = False   ,
    maximumDistance     = Nothing }

  pathFunctionFor (Piece.Knight) = markDjumpPath[0,1,2]

  pathFunctionFor (Piece.Bishop) = markLinearPath $ MovementLimitations {
    straightPathAllowed = False   ,
    diagonalPathAllowed = True    ,
    maximumDistance     = Nothing }

  pathFunctionFor (Piece.Queen) = markLinearPath $ MovementLimitations {
    straightPathAllowed = True    ,
    diagonalPathAllowed = True    ,
    maximumDistance     = Nothing }

  pathFunctionFor (Piece.King _) = markLinearPath $ MovementLimitations {
    straightPathAllowed = True    ,
    diagonalPathAllowed = True    ,
    maximumDistance     = Just 1  }

  move :: Location -> Game -> Maybe Game
  move destination (Game turnNumber turnColour selectedSquare boardMap)
    | isNothing selectedSquare = Nothing
    | otherwise = Game newTurnNumber newTurnColour Nothing <$> (ageAll <$> newBoardMap)
      where

        movingPiece :: Maybe Piece.Piece
        movingPiece = selectedSquare >>= (flip Map.lookup) boardMap

        newTurnNumber :: Int
        newTurnNumber = turnNumber + 1

        newTurnColour :: Piece.Colour
        newTurnColour = Piece.opponent turnColour

        newBoardMap :: Maybe BoardMap
        newBoardMap = selectedSquare >>= \startSquare -> (pathFunction movingPiece) startSquare destination $ captureOrTrample destination boardMap
          where
            pathFunction :: Maybe Piece.Piece -> Location -> Location -> BoardMap -> Maybe BoardMap
            pathFunction = fromMaybe(\ _ _ _ _ -> Nothing)(pathFunctionFor <$> (Piece.kind <$> movingPiece))
