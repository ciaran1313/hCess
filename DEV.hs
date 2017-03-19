import Game
import Move
import Path
import Location
import Piece
import CaptureOrTrample
import Select
import NewGame
import Control.Concurrent
import Status

instance Show Piece where
  show p = "----->" ++ asciiSymbol(Just p) ++ '(': (show $ previousLocation p) ++ " to " ++ (show $ nextLocation p) ++ (if isStop p then " - isStop" else []) ++ ")\n"

instance Show Game where
  show g = "turnNumber = " ++ show (turnNumber g) ++ "\nturnColour = " ++ show (turnColour g) ++ "\nselectedSquare = " ++ show (selectedSquare g) ++ "\n" ++ show (boardMap g)

gmvio = newMVar newGame
smvio = newMVar No_Issues
a1n = Location 0 0 0
