module Main where

  import Control.Concurrent
  import Control.Concurrent.MVar
  import Control.Monad

  import System.Exit

  import Text.Read

  import Data.List
  import Data.Maybe

  import qualified Game
  import qualified NewGame
  import Select
  import Move
  import Location
  import qualified Status

  import CommandLine.HelpMessage
  import CommandLine.Show

  main :: IO ()
  main = do {
    game_MVar <- newMVar NewGame.newGame;
    status_MVar <- newMVar Status.No_Issues;
    runCommand(game_MVar, status_MVar)["refresh"];
    forever $ do {
      game <- readMVar game_MVar;
      putStr $ prompt game;
      fmap words getLine >>= runCommand (game_MVar, status_MVar); --splits the input into its arguments and runs the command
    };
    return ();
  } where

      prompt :: Game.Game -> String
      prompt game = colour ++ selected ++ ": "
        where

          colour :: String
          colour = show $ Game.turnColour game

          selected :: String
          selected = fromMaybe[] $ fmap(\str -> "(" ++ str ++ ")")(show <$> Game.selectedSquare game)

      invalidCommand :: IO ()
      invalidCommand= do {
        putStrLn "Invalid command, or invalid arguments for command";
        return ();
      }

      invalidArgument :: String -> String -> IO ()
      invalidArgument arg str_type = putStrLn $ arg ++ " is not a valid " ++ str_type

      runCommand :: (MVar Game.Game, MVar Status.Status) -> [String] -> IO ()

    -- gameinfo
      runCommand(game_MVar, status_MVar)["gameinfo"] = readMVar game_MVar >>= (\game -> putStrLn $ info game)
        where
          info :: Game.Game -> String
          info game = ""
            ++ "turnNumber = " ++ (show $ Game.turnNumber game) ++ "\n"
            ++ "turnColour = " ++ (show $ Game.turnColour game) ++ "\n"
            ++ "selectedSquare = " ++ (show $ Game.selectedSquare game) ++ "\n"
            ++ "vis_t = " ++ (show $ Game.vis_t game) ++ "\n"
            ++ "vis_x = " ++ (show $ Game.vis_x game) ++ "\n"
            ++ "vis_y = " ++ (show $ Game.vis_y game) ++ "\n"

    --pause
      runCommand(game_MVar, status_MVar)["pause"] = do {
        putStrLn "Press ENTER to continue . . .";
        getLine;
        return ();
      }

    --help
      runCommand mvars ["help"] = do {
        putStrLn helpMessage;
        runCommand mvars ["pause"];
        runCommand mvars ["refresh"];
        return ();
      }

    --select
      runCommand mvars@(game_MVar, status_MVar) ["select", str_location] = if isJust maybe_location
        then do {
          select (fromJust maybe_location) mvars;
          status <- readMVar status_MVar;
          putStrLn (if status == Status.No_Issues
            then str_location ++ " successfully selected"
            else Status.message status
          );
        } else invalidArgument str_location "location"
          where
            maybe_location :: Maybe Location
            maybe_location = readMaybe str_location

    --deselect
      runCommand(game_MVar, status_MVar)["deselect"] = do {
        oldSelectedSquare <- Game.selectedSquare <$> readMVar game_MVar;
        deselect game_MVar;
        putStrLn $ fromMaybe "Nothing is selected" ((++ " successfully deselected") <$> fmap show oldSelectedSquare);
        swapMVar status_MVar Status.No_Issues;
        return ();
      }

    --moveto
      runCommand mvars@(game_MVar, status_MVar) ["moveto", str_location] = if isJust maybe_location
        then do {
          move (fromJust maybe_location) mvars;
          status <- readMVar status_MVar;
          if status == Status.No_Issues
            then runCommand mvars ["refresh"];
            else putStrLn $ Status.message status;
          return ();
        } else invalidArgument str_location "location"
        where
            maybe_location :: Maybe Location
            maybe_location = readMaybe str_location

  --move
      runCommand mvars@(game_MVar, status_MVar) ("move":arguments)
        | length filteredArguments /= 2 = invalidCommand
        | otherwise = do {
          runCommand mvars ["select", filteredArguments!!0];
          status <- readMVar status_MVar;
          (if status == Status.No_Issues
            then runCommand mvars ["moveto", filteredArguments!!1]
            else putStrLn $ Status.message status
          );
          return ();
        } where
            filteredArguments :: [String]
            filteredArguments = filter(/="to") arguments

    --view (explicit)
      runCommand(game_MVar, status_MVar)["view", str_new_vis_t, str_new_n, str_new_vis_x, str_new_vis_y] = do {
        game <- takeMVar game_MVar;
        putMVar game_MVar (Game.changeView (new_vis_t, new_n) new_vis_x new_vis_y game);
        runCommand(game_MVar, status_MVar)["refresh"];
        return ();
      } where

          new_vis_t, new_vis_x, new_vis_y :: Game.Coordinate
          new_vis_t = read str_new_vis_t
          new_vis_x = read str_new_vis_x
          new_vis_y = read str_new_vis_y

          new_n :: Int
          new_n = read str_new_n

    --view (implicit)
      runCommand mvars@(game_MVar, status_MVar) ["view", str_n] = do {
        game <- takeMVar game_MVar;
        if isNothing maybe_new_n -- if the new n is invalid input
          then invalidCommand; -- then it complains
          else do {
            putMVar game_MVar $ Game.changeView (new_vis_t, fromJust maybe_new_n) (new_vis_x game) (new_vis_y game) (game);
            runCommand mvars ["refresh"];
            return ();
          }
      } where

          new_vis_t :: Game.Coordinate
          new_vis_t = fromJust $ Game.identifyEnumFunctionIn str_n

          new_vis_x, new_vis_y :: Game.Game -> Game.Coordinate
          new_vis_x game
            | (Game.vis_x game) /= (new_vis_t) = (Game.vis_x game)
            | otherwise = (fst $ Game.vis_t game)
          new_vis_y game
            | (Game.vis_y game) /= (new_vis_t) = (Game.vis_y game)
            | otherwise = (fst $ Game.vis_t game)

          maybe_new_n :: Maybe Int
          maybe_new_n = (Game.deEnumFunctionFor new_vis_t) str_n

    --refresh
      runCommand (game_MVar, status_MVar) ["refresh"] = readMVar game_MVar >>= print

    --status
      runCommand (game_MVar, status_MVar) ["status"] = readMVar status_MVar >>= putStrLn . Status.message

    --quit
      runCommand _ ["quit"] = exitSuccess

    --restart
      runCommand _ ["restart"] = main

    --(ENTER)
      runCommand _ [] = return ()

    --(default)
      runCommand mvars _ = invalidCommand
