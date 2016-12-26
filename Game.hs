 module Game where

  import qualified Data.Map as Map
  import Piece
  import Location

  type BoardMap = Map.Map Location Piece

  data Game = Game {
    turnNumber    ::  Int                       ,
    turnColour    ::  Colour                    ,
    boardMap      ::  BoardMap                  }

  newGame :: Game
  newGame = Game 0 White makeBoardMap
    where
      makeBoardMap :: BoardMap
      makeBoardMap = Map.fromList(makeRoyalLine White 0 ++ makePawnLine White 1 ++ makeRoyalLine Black 7 ++ makePawnLine Black 6)
        where

          makeNewPiece :: Colour -> Kind -> Piece
          makeNewPiece c k = Piece c k Nothing Nothing

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

  getPieceAt :: Location -> Game -> Maybe Piece
  getPieceAt location game = Map.lookup location $ boardMap game
