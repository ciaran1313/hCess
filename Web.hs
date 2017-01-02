module Main where

  import Data.Maybe

  import Haste
  import Haste.DOM
  import Haste.Events

  import qualified HTMLF
  import CrossSection
  import Coordinate
  import Game
  import Select
  import Move
  import Location

  data RunParams = RunParams (Coordinate, Int) Coordinate Coordinate Game

  main :: IO ()
  main = do {
    runGame $ RunParams (T, 0) X Y newGame;
    return ();
  } where
      runGame :: MonadEvent m => RunParams -> m ()
      runGame oldParams@(RunParams (vis_t, n) vis_x vis_y game) = do {
        Just boardDiv <- elemById "board";
        board <- HTMLF.showCrossSection $ cutCrossSection (vis_t, n) vis_x vis_y game;
        allowMonadList $ map (addClickHandler oldParams) (filter HTMLF.clickable board);
        setChildren boardDiv $ map HTMLF.get_DOM_elem board;
        return ();
      } where

        allowMonadList :: MonadEvent m => [m HandlerInfo] -> m HandlerInfo
        allowMonadList = foldl1(\acc x -> do{acc;x;})

        addClickHandler :: MonadEvent m => RunParams -> HTMLF.BoardElem -> m HandlerInfo
        addClickHandler oldParams@(RunParams (vis_t, n) vis_x vis_y game) (HTMLF.Header new_vis_t new_n element) = onEvent element Click (\ _ -> runGame $ RunParams (new_vis_t, new_n) new_vis_x new_vis_y game)
          where
            new_vis_x, new_vis_y :: Coordinate
            new_vis_x
              | vis_x /= new_vis_t = vis_x
              | otherwise = vis_t
            new_vis_y
              | vis_y /= new_vis_t = vis_y
              | otherwise = vis_t
        addClickHandler oldParams@(RunParams (vis_t, n) vis_x vis_y game) (HTMLF.Square location element)
          | selectedSquare game == Nothing = onEvent element Click (\ _ -> runGame $ RunParams (vis_t, n) vis_x vis_y $ select location game)
          | selectedSquare game == Just location = onEvent element Click (\ _ -> runGame $ RunParams (vis_t, n) vis_x vis_y $ deselect game)
          | otherwise = onEvent element Click (\ _ -> runGame $ RunParams (vis_t, new_n) vis_x vis_y $ fromMaybe game gameAfterMove)
          where

            gameAfterMove :: Maybe Game
            gameAfterMove = move location game

            new_n :: Int
            new_n
              | isJust gameAfterMove && vis_t == T && n == turnNumber game = succ n
              | otherwise = n
