module Piece where

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

  instance Show Kind where
    show (Pawn _) = "Pawn"
    show (Rook _) = "Rook"
    show (Knight) = "Knight"
    show (Bishop) = "Bishop"
    show (Queen)  = "Queen"
    show (King _) = "King"

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

  setIsStop :: Piece -> Bool -> Piece
  setIsStop piece newIsStop = Piece {
    colour = colour piece                         ,
    kind = kind piece                             ,
    isStop = newIsStop                            ,
    nextLocation = nextLocation piece             ,
    previousLocation = previousLocation piece     }

  setNextLocation:: Piece -> Maybe Location -> Piece
  setNextLocation piece newNextLocation = Piece {
    colour = colour piece                         ,
    kind = kind piece                             ,
    isStop = isStop piece                         ,
    nextLocation = newNextLocation                ,
    previousLocation = previousLocation piece     }

  setPreviousLocation:: Piece -> Maybe Location -> Piece
  setPreviousLocation piece newPreviousLocation = Piece {
    colour = colour piece                         ,
    kind = kind piece                             ,
    isStop = isStop piece                         ,
    nextLocation = nextLocation piece             ,
    previousLocation = newPreviousLocation        }

  pathIndicator :: Piece -> Char
  pathIndicator p = if nextLocation p == Nothing then ' ' else if isStop p then '#' else '*'

  asciiSymbol, unicodeSymbol, htmlSymbol, defaultSymbol :: Maybe Piece -> String

  asciiSymbol Nothing = "   "
  asciiSymbol (Just p@(Piece c t _ _ _)) = [colourChar c, typeChar t, pathIndicator p]
    where

      colourChar :: Colour -> Char
      colourChar White  =   'W'
      colourChar Black  =   'B'

      typeChar :: Kind -> Char
      typeChar (Pawn _)   =   'P'
      typeChar (Rook _)   =   'R'
      typeChar (Knight)   =   'N'
      typeChar (Bishop)   =   'B'
      typeChar (Queen )   =   'Q'
      typeChar (King _)   =   'K'

  unicodeSymbol Nothing = "   "
  unicodeSymbol (Just p) = (symbolFor p) ++ (pathIndicator p) : " "
    where
      symbolFor :: Piece -> String
      symbolFor(Piece White (Pawn _)    _ _ _)    =   "♙"
      symbolFor(Piece White (Rook _)    _ _ _)    =   "♖"
      symbolFor(Piece White Knight      _ _ _)    =   "♘"
      symbolFor(Piece White Bishop      _ _ _)    =   "♗"
      symbolFor(Piece White Queen       _ _ _)    =   "♕"
      symbolFor(Piece White (King _)    _ _ _)    =   "♔"
      symbolFor(Piece Black (Pawn _)    _ _ _)    =   "♟"
      symbolFor(Piece Black (Rook _)    _ _ _)    =   "♜"
      symbolFor(Piece Black Knight      _ _ _)    =   "♞"
      symbolFor(Piece Black Bishop      _ _ _)    =   "♝"
      symbolFor(Piece Black Queen       _ _ _)    =   "♛"
      symbolFor(Piece Black (King _)    _ _ _)    =   "♚"

  htmlSymbol Nothing = "   "
  htmlSymbol (Just p) = (symbolFor p) ++ (pathIndicator p) : "&thinsp;"
    where
      symbolFor :: Piece -> String
      symbolFor(Piece White (Pawn _)    _ _ _)    =   "&#9817;"
      symbolFor(Piece White (Rook _)    _ _ _)    =   "&#9814;"
      symbolFor(Piece White Knight      _ _ _)    =   "&#9816"
      symbolFor(Piece White Bishop      _ _ _)    =   "&#9815;"
      symbolFor(Piece White Queen       _ _ _)    =   "&#9813;"
      symbolFor(Piece White (King _)    _ _ _)    =   "&#9812;"
      symbolFor(Piece Black (Pawn _)    _ _ _)    =   "&#9823;"
      symbolFor(Piece Black (Rook _)    _ _ _)    =   "&#9820;"
      symbolFor(Piece Black Knight      _ _ _)    =   "&#9822;"
      symbolFor(Piece Black Bishop      _ _ _)    =   "&#9821;"
      symbolFor(Piece Black Queen       _ _ _)    =   "&#9819;"
      symbolFor(Piece Black (King _)    _ _ _)    =   "&#9818;"

  defaultSymbol = asciiSymbol
