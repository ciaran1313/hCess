module Piece.Symbol where

  import Piece.Core (Piece(..), Colour(..), Kind(..), pathIndicator)

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
