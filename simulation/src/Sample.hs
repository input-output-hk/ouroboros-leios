{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedStrings #-}

module Sample where

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

data SampleEvent e = SampleEvent {time :: DiffTime, event :: e}
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
  runSampleModel' (Just traceFile) (\t -> fmap (toEncoding . SampleEvent t) . logEvent)

runSampleModel' ::
  forall event state.
  Maybe FilePath ->
  (DiffTime -> event -> Maybe Encoding) ->
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
    | otherwise = go (\(SimVizModel es st) -> return $ foldl' (\x (t, e) -> accum t e x) st es) m
  go :: (SimVizModel event state -> IO state) -> SimVizModel event state -> IO ()
  go w (SimVizModel es st) = case splitAt 10000 es of
    (before, after) -> do
      st' <- w (SimVizModel before st)
      case after of
        ((now, _) : _) -> do
          putStrLn $ "time reached: " ++ show now
          hFlush stdout
          go w (SimVizModel after st')
        [] -> do
          putStrLn "done."
          hFlush stdout
          render st'
  writeEvents _h (SimVizModel [] st) = return st
  writeEvents h (SimVizModel ((t'@(Time t), e) : es) st) = do
    case logEvent t e of
      Nothing -> return ()
      Just x -> do
        BSL.hPutStr h (encodingToLazyByteString x)
        BSL.hPutStr h "\n"
    writeEvents h (SimVizModel es (accum t' e st))
