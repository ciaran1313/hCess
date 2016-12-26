module Main where

  import Board
  import Haste
  import Haste.DOM
  import Haste.Events

  main :: IO()
  main = do{
    Just boardDiv <- elemById "board";
    set boardDiv [prop "innerHTML" =: "<b>Hello World</b>"];
    onEvent boardDiv Click $ \_ -> clearChildren document;
    return ();
  }
