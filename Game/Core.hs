 module Game.Core where

  import qualified Data.Map as Map (Map, insert, lookup)

  import Piece.Core (Piece, Colour)
  import Location (Location(..))
  import {-# SOURCE #-} Coordinate (Coordinate(..))

  type BoardMap = Map.Map Location Piece

  data Game = Game {
    turnNumber      ::  Int                       ,
    turnColour      ::  Colour                    ,
    selectedSquare  ::  Maybe Location            ,
    vis_t           :: (Coordinate, Int)          ,
    vis_x           ::  Coordinate                ,
    vis_y           ::  Coordinate                ,
    boardMap        ::  BoardMap                  }

  getPieceAt :: Game -> Location -> Maybe Piece
  getPieceAt game location = Map.lookup location (boardMap game)

  getSelectedPiece :: Game -> Maybe Piece
  getSelectedPiece game = selectedSquare game >>= getPieceAt game

  putPieceAt :: Game -> Location -> Piece -> Game
  putPieceAt game location piece = Game {
    turnNumber = turnNumber game                                    ,
    turnColour = turnColour game                                    ,
    selectedSquare = selectedSquare game                            ,
    vis_t = vis_t game                                              ,
    vis_x = vis_x game                                              ,
    vis_y = vis_y game                                              ,
    boardMap = Map.insert location piece (boardMap game)            }

  associatedLocation :: (Piece -> Maybe Location) -> Location -> BoardMap -> Maybe Location
  associatedLocation f location boardMap = Map.lookup location boardMap >>= f

  changeView :: (Coordinate, Int) -> Coordinate -> Coordinate -> Game -> Game
  changeView vis_t vis_x vis_y (Game turnNumber turnColour selectedSquare _ _ _ boardMap) = Game turnNumber turnColour selectedSquare vis_t vis_x vis_y boardMap

  lastIndexOf :: Coordinate -> (Game -> Int)
  lastIndexOf T = turnNumber
  lastIndexOf X = (\ _ -> 7)
  lastIndexOf Y = (\ _ -> 7)

  isWithinBoundsOfBoard :: Location -> Game -> Bool
  isWithinBoundsOfBoard (Location t x y) game = (t >= 0) && (x >= 0) && (y >= 0) && (t <= lastIndexOf T game) && (x <= lastIndexOf X game) && (y <= lastIndexOf Y game)
