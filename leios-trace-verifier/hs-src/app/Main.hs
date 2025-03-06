module Main where

import LeiosEvents
import Lib
import Data.ByteString.Lazy as BSL

logFile :: FilePath
logFile = "leios-trace.log"

main :: IO ()
main = BSL.readFile logFile >>= print . verifyTrace . decodeJSONL
