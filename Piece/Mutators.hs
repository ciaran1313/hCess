module Piece.Mutators where

  import Piece.Core (Piece(..))

  import Location (Location)

  setIsStop :: Piece -> Bool -> Piece
  setIsStop piece newIsStop = Piece {
    colour = colour piece                         ,
    kind = kind piece                             ,
    isStop = newIsStop                            ,
    nextLocation = nextLocation piece             ,
    previousLocation = previousLocation piece     }

  setNextLocation :: Piece -> Maybe Location -> Piece
  setNextLocation piece newNextLocation = Piece {
    colour = colour piece                         ,
    kind = kind piece                             ,
    isStop = isStop piece                         ,
    nextLocation = newNextLocation                ,
    previousLocation = previousLocation piece     }

  setPreviousLocation :: Piece -> Maybe Location -> Piece
  setPreviousLocation piece newPreviousLocation = Piece {
    colour = colour piece                         ,
    kind = kind piece                             ,
    isStop = isStop piece                         ,
    nextLocation = nextLocation piece             ,
    previousLocation = newPreviousLocation        }
