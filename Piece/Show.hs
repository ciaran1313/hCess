module Piece.Show where

    import Piece.Core (Kind(..))

    instance Show Kind where
      show (Pawn _) = "Pawn"
      show (Rook _) = "Rook"
      show (Knight) = "Knight"
      show (Bishop) = "Bishop"
      show (Queen)  = "Queen"
      show (King _) = "King"
