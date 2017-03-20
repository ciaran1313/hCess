module Aging where

  import qualified Data.Map as Map (union, filter, filterWithKey, lookup, mapKeys, mapWithKey)
  import Data.Maybe (isNothing)
  import Game.Core (Game(..), BoardMap)
  import Location (Location(..))
  import Piece.Core (Piece(..), opponent)
  import Coordinate (Coordinate(..))

  age :: Game -> Game
  age game = template game (ageBoardMap $ boardMap game)
    where

      template :: Game -> BoardMap -> Game
      template game newBoardMap = Game {
        turnNumber = succ $ turnNumber game,
        turnColour = opponent $ turnColour game,
        selectedSquare = Nothing,
        vis_t = (fst $ vis_t game, if (==)(T)(fst $ vis_t game) then (succ)(snd $ vis_t game) else (snd)(vis_t game)),
        vis_x = vis_x game,
        vis_y = vis_y game,
        boardMap = newBoardMap  }

      ageBoardMap :: BoardMap -> BoardMap
      ageBoardMap boardMap = Map.union combinedRoster boardMap
        where

          ageLocation :: Location -> Location
          ageLocation location = Location {
            t_value = t_value location + 1    ,
            x_value = x_value location        ,
            y_value = y_value location        }

          unprocessedRoster :: BoardMap
          unprocessedRoster = Map.filterWithKey(\k _ -> isNothing $ Map.lookup (ageLocation k) boardMap) $ Map.filter(isNothing . nextLocation) boardMap

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
