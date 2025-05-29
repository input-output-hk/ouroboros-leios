{-# LANGUAGE OverloadedStrings #-}

module Leios.Tracing.Processor (
  process
) where

import Leios.Tracing.Lifecycle (lifecycle)

import qualified Data.Aeson as A
import qualified Data.ByteString.Lazy as LBS
import qualified Data.ByteString.Lazy.Char8 as LBS8

process :: FilePath -> FilePath -> IO ()
process logFile lifecycleFile =
  do
    logEntries <- LBS8.lines <$> LBS.readFile logFile
    lifecycle lifecycleFile $ nextEntry logEntries

nextEntry :: [LBS8.ByteString] -> [A.Value]
nextEntry [] = []
nextEntry (event : events) =
  case A.eitherDecode event of
    Right event' -> event' : nextEntry events
    Left message -> error $ "[" <> LBS8.unpack event <> "|" <> message <> "]"
