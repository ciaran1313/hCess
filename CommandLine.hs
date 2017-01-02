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
    ++ "help - print this helpMessage\n\n"
    ++ "select [LOCATION] - selects a square on the board\n\n"
    ++ "moveto [LOCATION] - moves the piece at the selected square to the specified LOCATION\n\n"
    ++ "move [START] (\"to\") [DESTINATION] - moves the piece at the START to the DESTINATION\n\n"
    ++ "view [VIS_T] [N] [VIS_X] [VIS_Y] - sets the perspective of the board such that VIS_X is presented horizontally, VIS_Y is presented vertically, and the entire board being presented under VIS_T at level [N]\n\n"
    ++ "view [LEVEL] - sets the perspective of the board. Infers VIS_T VIS_X and VIS_Y by weather LEVEL is a letter, a digit, or a roman numeral\n\n"
    ++ "quit - quits the game\n\n"

  data RunParams = RunParams (Coordinate, Int) Coordinate Coordinate Game

  pause :: IO ()
  pause = do {
    putStrLn "(PRESS ENTER TO CONTINUE)";
    getLine;
    return ();
  }

  main :: IO ()
  main = runGame $ RunParams (T, 0) X Y newGame
    where
      runGame :: RunParams -> IO ()
      runGame oldParams@(RunParams (vis_t, n) vis_x vis_y game) = do {
        print $ cutCrossSection (vis_t, n) vis_x vis_y game; --prints the board
        putStrLn $ (++ ":")(show $ turnColour game); --prompts the player with the name of their colour
        fmap words getLine >>= runCommand; --splits the input into its arguments and runs the command
      } where

          complain :: IO ()
          complain = do {
            putStrLn "Invalid command, or invalid number of arguments for command";
            pause;
            runGame oldParams;
          }

          runCommand :: [String] -> IO ()

          runCommand[] = runGame oldParams

          runCommand["help"] = do {
            putStrLn helpMessage;
            pause;
            runGame oldParams;
          }

          runCommand["select", str_location] = runGame $ RunParams (vis_t, n) vis_x vis_y (select location game)
            where
              location :: Location
              location = read str_location

          runCommand["deselect"] = runGame $ RunParams (vis_t, n) vis_x vis_y (deselect game)

          runCommand["moveto", str_location] = runGame $ fromMaybe oldParams $ RunParams (vis_t, new_n) vis_x vis_y <$> move location game
            where
              location :: Location
              location = read str_location

              new_n :: Int
              new_n
                | (==)(vis_t)(T) && (==)(turnNumber game)(n) = n + 1
                | otherwise = n

          runCommand("move":arguments)
            | length filteredArguments == 2 = runGame $ fromMaybe oldParams $ RunParams (vis_t, new_n) vis_x vis_y <$> (move destination . select startSquare) game
            | otherwise = complain
            where

              filteredArguments :: [String]
              filteredArguments = filter(/="to") arguments

              startSquare, destination :: Location
              startSquare = read $ filteredArguments !! 0
              destination = read $ filteredArguments !! 1

              new_n :: Int
              new_n
                | (==)(vis_t)(T) && (==)(turnNumber game)(n) = n + 1
                | otherwise = n


          runCommand["view", str_new_vis_t, str_new_n, str_new_vis_x, str_new_vis_y] = runGame $ RunParams (new_vis_t, new_n) vis_x vis_y game
            where
              new_vis_t, new_vis_x, new_vis_y :: Coordinate
              new_vis_t = read str_new_vis_t
              new_vis_x = read str_new_vis_x
              new_vis_y = read str_new_vis_y

              new_n :: Int
              new_n = read str_new_n

          runCommand["view", str_n] = runGame $ fromMaybe oldParams $ (\t n -> RunParams (t, n) new_vis_x new_vis_y game) <$> new_vis_t <*> new_n
            where

              new_vis_t :: Maybe Coordinate
              new_vis_t = identifyEnumFunctionIn str_n

              new_vis_x, new_vis_y :: Coordinate
              new_vis_x
                | Just vis_x /= new_vis_t = vis_x
                | otherwise = vis_t
              new_vis_y
                | Just vis_y /= new_vis_t = vis_y
                | otherwise = vis_t

              new_n :: Maybe Int
              new_n = new_vis_t >>= (flip deEnumFunctionFor str_n)

          runCommand["quit"] = return ()

          runCommand _ = complain
