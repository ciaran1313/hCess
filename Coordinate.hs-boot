module Coordinate where

  data Coordinate = T | X | Y

  toFile :: Int -> Char
  toRank :: Int -> Char
  toTurn :: Int -> String
  fromFile :: String -> Maybe Int
  fromRank :: String -> Maybe Int
  fromTurn :: String -> Maybe Int
