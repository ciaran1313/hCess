 module Game where

  import qualified Data.Map as Map (Map, insert, lookup)

  import Piece (Piece, Colour)
  import Location (Location)
  import {-# SOURCE #-} Coordinate (Coordinate)

  type BoardMap = Map.Map Location Piece

  data Game = Game {
    turnNumber      ::  Int                       ,
    turnColour      ::  Colour                    ,
    selectedSquare  ::  Maybe Location            ,
    vis_t           :: (Coordinate, Int)          ,
    vis_x           ::  Coordinate                ,
    vis_y           ::  Coordinate                ,
    boardMap        ::  BoardMap                  }

  setTurnNumber :: Game -> Int -> Game
  setTurnNumber game newTurnNumber = Game {
    turnNumber = newTurnNumber            ,
    turnColour = turnColour game          ,
    selectedSquare = selectedSquare game  ,
    vis_t = vis_t game                    ,
    vis_x = vis_x game                    ,
    vis_y = vis_y game                    ,
    boardMap = boardMap game              }

  setTurnColour :: Game -> Colour -> Game
  setTurnColour game newTurnColour = Game {
    turnNumber = turnNumber game          ,
    turnColour = newTurnColour            ,
    selectedSquare = selectedSquare game  ,
    vis_t = vis_t game                    ,
    vis_x = vis_x game                    ,
    vis_y = vis_y game                    ,
    boardMap = boardMap game              }

  setSelectedSquare :: Game -> Maybe Location -> Game
  setSelectedSquare game newSelectedSquare = Game {
    turnNumber = turnNumber game          ,
    turnColour = turnColour game          ,
    selectedSquare = newSelectedSquare    ,
    vis_t = vis_t game                    ,
    vis_x = vis_x game                    ,
    vis_y = vis_y game                    ,
    boardMap = boardMap game              }

  setBoardMap :: Game -> BoardMap -> Game
  setBoardMap game newBoardMap = Game {
    turnNumber = turnNumber game          ,
    turnColour = turnColour game          ,
    selectedSquare = selectedSquare game  ,
    vis_t = vis_t game                    ,
    vis_x = vis_x game                    ,
    vis_y = vis_y game                    ,
    boardMap = newBoardMap                }

  getPieceAt :: Game -> Location -> Maybe Piece
  getPieceAt game location = Map.lookup location (boardMap game)

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
