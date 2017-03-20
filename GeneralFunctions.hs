module GeneralFunctions where

  import Control.Concurrent.MVar (MVar, takeMVar, putMVar)

  applyToMVar ::  MVar a -> (a -> a) -> IO ()
  applyToMVar x f = takeMVar x >>= putMVar x . f
