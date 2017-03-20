module NewGame where

  import qualified Data.Map as Map (fromList)

  import Game.Core (Game(..), BoardMap(..))
  import Piece.Core (Piece(..), Colour(..), Kind(..), virginPawn, virginRook, virginKing)
  import Location (Location(..))
  import Coordinate (Coordinate(..))

  newGame :: Game
  newGame = Game {
    turnNumber = 0            ,
    turnColour = White        ,
    selectedSquare = Nothing  ,
    vis_t = (T, 0)            ,
    vis_x = X                 ,
    vis_y = Y                 ,
    boardMap = makeBoardMap   }
    where
      makeBoardMap :: BoardMap
      makeBoardMap = Map.fromList(makeRoyalLine White 0 ++ makePawnLine White 1 ++ makeRoyalLine Black 7 ++ makePawnLine Black 6)
        where

          makeNewPiece :: Colour -> Kind -> Piece
          makeNewPiece c k = Piece {
            colour            = c         ,
            kind              = k         ,
            isStop            = True      ,
            nextLocation      = Nothing   ,
            previousLocation  = Nothing   }

          makePawnLine :: Colour -> Int -> [(Location, Piece)]
          makePawnLine colour y = zip (map(\x -> Location 0 x y)[0..7]) (repeat $ makeNewPiece colour virginPawn)

          makeRoyalLine :: Colour -> Int -> [(Location, Piece)]
          makeRoyalLine colour y = [
            (Location 0 0 y, makeNewPiece colour virginRook   ),
            (Location 0 1 y, makeNewPiece colour Knight       ),
            (Location 0 2 y, makeNewPiece colour Bishop       ),
            (Location 0 3 y, makeNewPiece colour Queen        ),
            (Location 0 4 y, makeNewPiece colour virginKing   ),
            (Location 0 5 y, makeNewPiece colour Bishop       ),
            (Location 0 6 y, makeNewPiece colour Knight       ),
            (Location 0 7 y, makeNewPiece colour virginRook   )]
