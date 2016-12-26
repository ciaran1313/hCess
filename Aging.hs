module Aging where

  import qualified Data.Map as Map
  import Data.Maybe
  import Game (BoardMap)
  import Location
  import Piece

  ageAll :: BoardMap -> BoardMap
  ageAll boardMap = Map.union combinedRoster boardMap
    where

      unprocessedRoster :: BoardMap
      unprocessedRoster = Map.filter(isNothing . nextLocation) boardMap

      ageLocation :: Location -> Location
      ageLocation location = Location {
        t_value = t_value location + 1    ,
        x_value = x_value location        ,
        y_value = y_value location        }

      agedRoster :: BoardMap
      agedRoster = (Map.mapKeys ageLocation . Map.mapWithKey agePiece) unprocessedRoster
        where
          agePiece :: Location -> Piece -> Piece
          agePiece locationOfPiece piece = Piece {
            colour            =   colour piece                          ,
            kind              =   kind piece                            ,
            isStop            =   True                                  ,
            nextLocation      =   Nothing                               ,
            previousLocation  =   Just locationOfPiece                  }

      preagedRoster :: BoardMap
      preagedRoster = Map.mapWithKey preagePiece unprocessedRoster
        where
          preagePiece :: Location -> Piece -> Piece
          preagePiece locationOfPiece piece = Piece {
            colour            =   colour piece                         ,
            kind              =   kind piece                           ,
            isStop            =   True                                 ,
            nextLocation      =   Just $ ageLocation locationOfPiece   ,
            previousLocation  =   previousLocation piece               }

      combinedRoster :: BoardMap
      combinedRoster = Map.union agedRoster preagedRoster
