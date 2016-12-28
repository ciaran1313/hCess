module Main where

  import Data.List
  import Data.Maybe
  import Game
  import Move
  import Coordinate
  import CrossSection
  import Location

  helpMessage :: String
  helpMessage = "Enter your move. (Example: \"move b2n to b4n\" or \"move h6ii g6iv\")"

  type RunParams = ((Coordinate, Int), Coordinate, Coordinate, Game)

  newParams :: RunParams -> [Location] -> RunParams
  newParams oldParams@((vis_t, n), vis_x, vis_y, game) [startSquare, destination]
    | isNothing newGameState = oldParams
    | otherwise = ((vis_t, new_n), vis_x, vis_y, fromJust newGameState)
    where

      newGameState :: Maybe Game
      newGameState = move startSquare destination game

      new_n :: Int
      new_n
        | (vis_t == T && n == turnNumber game) = n + 1
        | otherwise = n

  pause :: IO ()
  pause = do {
    putStrLn "(PRESS ENTER TO CONTINUE)";
    getLine;
    return ();
  }

  main :: IO ()
  main = runGame ((T,0), X, Y, newGame)
    where
      runGame :: RunParams -> IO ()
      runGame oldParams@((vis_t, n), vis_x, vis_y, game) = do {
        print $ cutCrossSection (vis_t, n) vis_x vis_y game;
        putStrLn $ (++ ":")(show $ turnColour game);
        argv <- fmap words getLine;
        if length argv <= 1
          then runGame oldParams
          else
            let argc = length argv in
              case head argv of

                "help" -> if argc == 1
                  then do {
                    putStrLn helpMessage;
                    pause;
                    runGame oldParams;
                  } else badargc;

                "move" -> if argc >= 3
                  then runGame $ newParams oldParams $ (map read . filter (/= "to") . tail :: [String] -> [Location]) argv;
                  else badargc;

                "view" -> if argc == 5
                  then runGame ((new_vis_t, new_n), new_vis_x, new_vis_y, game)
                  else badargc
                  where
                    new_vis_t, new_vis_x, new_vis_y :: Coordinate
                    new_vis_t = read $ argv !! 1
                    new_vis_x = read $ argv !! 3
                    new_vis_y = read $ argv !! 4

                    new_n :: Int
                    new_n = read $ argv !! 2

                _ -> do {
                  putStrLn $ "Please enter a valid command. (Example: \"help\")";
                  pause;
                  runGame oldParams;
              }
      } where
          badargc :: IO ()
          badargc = do {
            putStrLn "Invalid number of arguments";
            pause;
            runGame oldParams;
          }
