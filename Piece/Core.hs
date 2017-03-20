module Piece.Core where

  import Location (Location)

  data Colour = White | Black
    deriving (Eq, Show)

  opponent :: Colour -> Colour
  opponent White = Black
  opponent Black = White

  data Kind = Pawn {hasMoved :: Bool}
            | Rook {hasMoved :: Bool}
            | Knight
            | Bishop
            | Queen
            | King {hasMoved :: Bool}
    deriving (Eq)

  virginPawn, virginRook, virginKing :: Kind
  virginPawn = Pawn {hasMoved = False}
  virginRook = Rook {hasMoved = False}
  virginKing = King {hasMoved = False}

  data Piece = Piece {
      colour                ::    Colour              ,
      kind                  ::    Kind                ,
      isStop                ::    Bool                ,
      nextLocation          ::    (Maybe Location)    ,
      previousLocation      ::    (Maybe Location)    }
    deriving (Eq)

  pathIndicator :: Piece -> Char
  pathIndicator p = if nextLocation p == Nothing then ' ' else if isStop p then '#' else '*'
