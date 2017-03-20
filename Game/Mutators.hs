module Game.Mutators where

  import Game.Core (Game(..), BoardMap)
  import Piece.Core (Colour)
  import Location (Location)

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
