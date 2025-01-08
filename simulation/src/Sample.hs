{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}

module Sample where

import Data.Aeson
import Data.Aeson.Text (encodeToLazyText)
import Data.List (foldl')
import qualified Data.Text.Lazy.IO as T
import GHC.Generics
import System.IO (IOMode (WriteMode), hFlush, stdout, withFile)
import TimeCompat
import VizSim

data SampleModel event state = SampleModel
  { initState :: state
  , accumState :: Time -> event -> state -> state
  , renderState :: state -> IO ()
  }

data SampleEvent e = SampleEvent {time :: Time, event :: e}
  deriving (Generic, ToJSON)

runSampleModel ::
  ToJSON a =>
  FilePath ->
  (event -> Maybe a) ->
  SampleModel event state ->
  Time ->
  [(Time, event)] ->
  IO ()
runSampleModel traceFile logEvent (SampleModel s0 accum render) stop =
  process . flip SimVizModel s0 . takeWhile (\(t, _) -> t <= stop)
 where
  process m = withFile traceFile WriteMode (flip go m)
  go h m = case stepSimViz 10000 m of
    (before, m'@(SimVizModel ((now, _) : _) _)) -> do
      writeEvents h before
      putStrLn $ "time reached: " ++ show now
      hFlush stdout
      go h m'
    (before, SimVizModel [] s) -> do
      writeEvents h before
      putStrLn "done."
      render s
  stepSimViz n (SimVizModel es s) = case splitAt n es of
    (before, after) -> (,) before $ SimVizModel after (foldl' (\x (t, e) -> accum t e x) s before)
  writeEvents h es = flip mapM_ es $ \(t, e) ->
    case logEvent e of
      Nothing -> return ()
      Just x -> T.hPutStrLn h (encodeToLazyText (SampleEvent t x))
