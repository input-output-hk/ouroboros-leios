{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedStrings #-}

module Sample where

import Control.Monad
import Data.Aeson
import Data.Aeson.Encoding
import qualified Data.ByteString.Lazy as BSL
import Data.List (foldl')
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
runSampleModel traceFile logEvent =
  runSampleModel' (Just traceFile) (fmap toEncoding . logEvent)

runSampleModel' ::
  forall event state.
  Maybe FilePath ->
  (event -> Maybe Encoding) ->
  SampleModel event state ->
  Time ->
  [(Time, event)] ->
  IO ()
runSampleModel' traceFile logEvent (SampleModel s0 accum render) stop =
  process . flip SimVizModel s0 . takeWhile (\(t, _) -> t <= stop)
 where
  process m
    | Just f <- traceFile =
        withFile f WriteMode $ (`go` m) . writeEvents
    | otherwise = go (const $ pure ()) m
  go :: ([(Time, event)] -> IO ()) -> SimVizModel event state -> IO ()
  go w m = case stepSimViz 10000 m of
    (before, m'@(SimVizModel ((now, _) : _) _)) -> do
      w before
      putStrLn $ "time reached: " ++ show now
      hFlush stdout
      go w m'
    (before, SimVizModel [] s) -> do
      w before
      putStrLn "done."
      render s
  stepSimViz n (SimVizModel es s) = case splitAt n es of
    (before, after) -> (,) before $ SimVizModel after (foldl' (\x (t, e) -> accum t e x) s before)
  writeEvents h es = forM_ es $ \(Time t, e) ->
    case logEvent e of
      Nothing -> return ()
      Just x -> do
        BSL.hPutStr h (encodingToLazyByteString (pairs $ "time_s" .= t <> pair "event" x))
        BSL.hPutStr h "\n"
