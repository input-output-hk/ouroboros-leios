{-# LANGUAGE OverloadedStrings #-}

module Leios.Tracing.Processor (
  process,
) where

import Control.Concurrent.Chan (Chan, dupChan, newChan, writeChan)
import Control.Concurrent.MVar (newEmptyMVar, putMVar, readMVar)
import Control.Concurrent.Async (concurrently_, mapConcurrently_)
import Leios.Tracing.Cpu (cpu)
import Leios.Tracing.Lifecycle (lifecycle)

import qualified Data.Aeson as A
import qualified Data.ByteString.Lazy as LBS
import qualified Data.ByteString.Lazy.Char8 as LBS8

process :: FilePath -> FilePath -> FilePath -> IO ()
process logFile lifecycleFile cpuFile =
  do
    done <- newEmptyMVar
    chan <- newChan
    let reader =
          do
            logEntries <- LBS8.lines <$> LBS.readFile logFile
            nextEntry chan logEntries
            readMVar done
    concurrently_ reader
      $ mapConcurrently_ id
        [
          lifecycle lifecycleFile chan
        , dupChan chan >>= cpu cpuFile
        ]
      >> putMVar done ()

nextEntry :: Chan (Maybe A.Value) -> [LBS8.ByteString] -> IO ()
nextEntry eventChan [] = writeChan eventChan Nothing >> pure ()
nextEntry eventChan (event : events) =
  case A.eitherDecode event of
    Right event' -> writeChan eventChan (Just event') >> nextEntry eventChan events
    Left message -> error $ "[" <> LBS8.unpack event <> "|" <> message <> "]"
