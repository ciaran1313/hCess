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

  pathFunctionFor :: Piece.Kind -> Bool -> (Maybe Piece.Piece -> Location -> Location -> BoardMap -> Maybe BoardMap)

  pathFunctionFor (Piece.Pawn hasMoved) isCapture = pathFunctionForPawn
    where
      pathFunctionForPawn :: Maybe Piece.Piece -> Location -> Location -> BoardMap -> Maybe BoardMap
      pathFunctionForPawn piece startSquare destination boardMap = pathFunctionForPawn' newPiece startSquare destination boardMap
        where

          pathFunctionForPawn' :: Maybe Piece.Piece -> Location -> Location -> BoardMap -> Maybe BoardMap
          pathFunctionForPawn' = markLinearPath $ MovementLimitations {
            straightPathAllowed = not isCapture                                   , --pawns cannot capture through straigh path
            diagonalPathAllowed = isCapture                                       , --pawns cannot take a diagonal path with no capture
            maximumDistance     = Just (if hasMoved || isCapture then 1 else 2)   } --if a pawn has moved or its performing a capture, it can only move 1 square. If its its first move and it's not performig a capture, it can move

          newPiece ::  Maybe Piece.Piece
          newPiece = (\c -> Piece.Piece {
              Piece.colour = c                                      ,
              Piece.kind = newPieceKind                             ,
              Piece.isStop = False                                  ,
              Piece.nextLocation = Nothing                          ,
              Piece.previousLocation = Nothing                      }) <$> (Piece.colour <$> piece)
              where
                newPieceKind :: Piece.Kind
                newPieceKind = Piece.Pawn {Piece.hasMoved = True}

  pathFunctionFor (Piece.Rook _) _ = markLinearPath $ MovementLimitations {
    straightPathAllowed = True    ,
    diagonalPathAllowed = False   ,
    maximumDistance     = Nothing }

  pathFunctionFor (Piece.Knight) _ = markDjumpPath[0,1,2]

  pathFunctionFor (Piece.Bishop) _ = markLinearPath $ MovementLimitations {
    straightPathAllowed = False   ,
    diagonalPathAllowed = True    ,
    maximumDistance     = Nothing }

  pathFunctionFor (Piece.Queen) _ = markLinearPath $ MovementLimitations {
    straightPathAllowed = True    ,
    diagonalPathAllowed = True    ,
    maximumDistance     = Nothing }

  pathFunctionFor (Piece.King _) _ = markLinearPath $ MovementLimitations {
    straightPathAllowed = True    ,
    diagonalPathAllowed = True    ,
    maximumDistance     = Just 1  }

  move :: Location -> Game -> Maybe Game
  move destination game@(Game turnNumber turnColour selectedSquare boardMap)
    | nothingIsSelected = Nothing
    | isCapture && pieceAtDestinationBelongsToThePlayer = Nothing
    | otherwise = Game newTurnNumber newTurnColour Nothing <$> (ageAll <$> newBoardMap)
      where

        movingPiece :: Maybe Piece.Piece
        movingPiece = selectedSquare >>= (flip Map.lookup) boardMap

        newTurnNumber :: Int
        newTurnNumber = turnNumber + 1

        newTurnColour :: Piece.Colour
        newTurnColour = Piece.opponent turnColour

        isCapture, pieceAtDestinationBelongsToThePlayer :: Bool
        nothingIsSelected = isNothing selectedSquare
        isCapture = fromMaybe False (Piece.isStop <$> Map.lookup destination boardMap)
        pieceAtDestinationBelongsToThePlayer = (==)(Piece.colour <$> getPieceAt destination game)(Just turnColour)

        newBoardMap :: Maybe BoardMap
        newBoardMap = selectedSquare >>= (\startSquare -> pathFunction isCapture movingPiece startSquare destination $ captureOrTrample destination boardMap)
          where
            pathFunction :: Bool -> Maybe Piece.Piece -> Location -> Location -> BoardMap -> Maybe BoardMap
            pathFunction = fromMaybe(\ _ _ _ _ _ -> Nothing)(pathFunctionFor <$> (Piece.kind <$> movingPiece))
