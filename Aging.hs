module Aging where

  import qualified Data.Map as Map
  import Data.Maybe
  import Game (BoardMap)
  import Location
  import Piece

  ageAll :: BoardMap -> BoardMap
  ageAll boardMap = boardMap
    where

      preagePiece :: Location -> Piece -> Piece
      preagePiece locationOfPiece piece = Piece {
        colour            =   colour piece                         ,
        kind              =   kind piece                           ,
        nextLocation      =   Just $ ageLocation locationOfPiece   ,
        previousLocation  =   previousLocation piece               }

      agePiece :: Location -> Piece -> Piece
      agePiece locationOfPiece piece = Piece {
        colour            =   colour piece                         ,
        kind              =   kind piece                           ,
        nextLocation      =   Nothing                              ,
        previousLocation  =   Just locationOfPiece                 }

      ageLocation :: Location -> Location
      ageLocation location = Location {
        t_value = t_value location + 1    ,
        x_value = x_value location        ,
        y_value = y_value location        }

      roster :: BoardMap
      roster = Map.filter(isNothing . nextLocation) boardMap

      agedRoster :: BoardMap
      agedRoster = roster

      preagedBoardMap :: BoardMap
      preagedBoardMap = Map.mapWithKey preagePiece roster
