{-# LANGUAGE OverloadedStrings #-}

module Leios.Tracing.Processor (
  process,
) where

import Control.Concurrent.Async (concurrently_, mapConcurrently_)
import Control.Concurrent.MVar (MVar, newEmptyMVar, putMVar, readMVar)
import Control.Monad (forM_)
import Leios.Tracing.Cpu (cpu)
import Leios.Tracing.Lifecycle (lifecycle)
import Leios.Tracing.Receipt (receipt)
import Leios.Tracing.Resource (resource)

import qualified Data.Aeson as A
import qualified Data.ByteString.Lazy as LBS
import qualified Data.ByteString.Lazy.Char8 as LBS8

process :: FilePath -> FilePath -> FilePath -> FilePath -> FilePath -> IO ()
process logFile lifecycleFile cpuFile resourceFile receiptFile =
  do
    done <- newEmptyMVar
    cpuMVar <- newEmptyMVar
    lifecycleMVar <- newEmptyMVar
    receiptMVar <- newEmptyMVar
    resourceMVar <- newEmptyMVar
    let reader =
          do
            logEntries <- LBS8.lines <$> LBS.readFile logFile
            nextEntry [cpuMVar, lifecycleMVar, receiptMVar, resourceMVar] logEntries
            readMVar done
    concurrently_ reader $
      mapConcurrently_
        id
        [ cpu cpuFile cpuMVar
        , lifecycle lifecycleFile lifecycleMVar
        , receipt receiptFile receiptMVar
        , resource resourceFile resourceMVar
        ]
        >> putMVar done ()

nextEntry :: [MVar (Maybe A.Value)] -> [LBS8.ByteString] -> IO ()
nextEntry eventMVars [] = forM_ eventMVars (`putMVar` Nothing) >> pure ()
nextEntry eventMVars (event : events) =
  case A.eitherDecode event of
    Right event' -> forM_ eventMVars (`putMVar` Just event') >> nextEntry eventMVars events
    Left message -> error $ "[" <> LBS8.unpack event <> "|" <> message <> "]"
