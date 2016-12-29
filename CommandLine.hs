module Main where

  import Data.List
  import Data.Maybe
  import Game
  import Select
  import Move
  import Coordinate
  import CrossSection
  import Location

  helpMessage :: String
  helpMessage = ""
    ++ "help - print this helpMessage\n"
    ++ "select [LOCATION] - selects a square on the board\n"
    ++ "moveto [LOCATION] - moves the piece at the selected square to the specified LOCATION"
    ++ "view [VIS_T] [N] [VIS_X] [VIS_Y] - sets the perspective of the board such that VIS_X is presented horizontally, VIS_Y is presented vertically, and the entire board being presented under VIS_T at level [N]"


  type RunParams = ((Coordinate, Int), Coordinate, Coordinate, Game)

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

                "select" -> if argc == 2
                  then runGame ((vis_t, n), vis_x, vis_y, select (read (argv!!1) :: Location) game)
                  else badargc;

                "moveto" -> if argc == 2
                  then if isJust $ move (read (argv!!1) :: Location) game
                    then runGame ((vis_t, n + if vis_t == T && n == turnNumber game then 1 else 0), vis_x, vis_y, fromJust $ move (read (argv!!1) :: Location) game)
                    else runGame oldParams;
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
