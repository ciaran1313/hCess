import Game
import CrossSection
import Move
import Path
import Location
import RelativePosition
import Coordinate
import Piece

instance Show Piece where
  show p = "----->" ++ asciiSymbol(Just p) ++ '(': (show $ previousLocation p) ++ " to " ++ (show $ nextLocation p) ++ ")\n"

instance Show Game where
  show g = "turnNumber = " ++ show (turnNumber g) ++ "\nturnColour = " ++ show (turnColour g) ++ "\n" ++ show (boardMap g)
