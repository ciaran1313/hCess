module MovementLimitations where

  data MovementLimitations = MovementLimitations{
    straightPathAllowed :: Bool       ,
    diagonalPathAllowed :: Bool       ,
    maximumDistance     :: Int        }
