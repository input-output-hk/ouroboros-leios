module Main where

import Data.ByteString.Lazy as BSL
import LeiosEvents
import Lib

logFile :: FilePath
logFile = "leios-trace.log"

main :: IO ()
main = BSL.readFile logFile >>= print . verifyTrace . decodeJSONL
