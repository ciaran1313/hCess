module Main where

  import Data.List
  import Data.Maybe
  import Game
  import Move
  import Coordinate
  import CrossSection
  import Location

  parseMove :: String -> [Location]
  parseMove = map read . filter(/="to") . words

  helpMessage :: IO ()
  helpMessage = putStrLn "Enter your move. (Example \"b2n to b4n\" or \"h6ii g6iv\")"

  getMove :: IO [Location]
  getMove = do {
    input <- getLine;
    if input == "?" || input == "help"
      then do {
        helpMessage;
        getMove;
      }
      else
        let moveList = parseMove input in
          if length moveList == 2
            then return moveList
            else do{
              putStrLn "INVALID INPUT. (try ? or help)";
              getMove;
            }
          ;
  }

  type RunParams = ((Coordinate, Int), Coordinate, Coordinate, Game)

  newParams :: RunParams -> [Location] -> RunParams
  newParams oldParams@((vis_t, n), vis_x, vis_y, game) [startSquare, destination]
    | isNothing newGameState = oldParams
    | otherwise = ((vis_t, new_n), vis_x, vis_y, fromJust newGameState)
    where

      newGameState :: Maybe Game
      newGameState = move startSquare destination game

      new_n :: Int
      new_n = n + 1


  main :: IO ()
  main = runGame ((T,0), X, Y, newGame)
    where
      runGame :: RunParams -> IO ()
      runGame oldParams@((vis_t, n), vis_x, vis_y, game) = do {
        print $ cutCrossSection (vis_t, n) vis_x vis_y game;
        putStrLn $ (++ ":")(show $ turnColour game);
        moveList <- getMove;
        runGame $ newParams oldParams moveList;
      }
