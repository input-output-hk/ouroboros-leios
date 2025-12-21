module Main where


import Data.Int (Int64)
import System.IO (stdout)

import qualified Data.ByteString.Builder as BB
import qualified Data.ByteString.Lazy as BL
import qualified Data.ByteString.Lazy.Char8 as BL8


encodeEdge :: Int64 -> Int64 -> Double -> Double -> BB.Builder
encodeEdge u v w w' = 
    BB.int64LE u <> 
    BB.int64LE v <> 
    BB.doubleLE w <>
    BB.doubleLE w'

processLine :: BL.ByteString -> BB.Builder
processLine line = 
    let parts = BL8.split '\t' line
        u = read (BL8.unpack (parts !! 1)) :: Int64
        v = read (BL8.unpack (parts !! 2)) :: Int64
        w = read (BL8.unpack (parts !! 3)) :: Double
        w' = read (BL8.unpack (parts !! 4)) :: Double
    in encodeEdge u v w w'

main :: IO ()
main = do
    input <- BL.getContents
    let lines' = drop 1 $ BL8.lines input
    let binaryStream = map processLine lines'
    let outputBytes = BB.toLazyByteString (mconcat binaryStream)
    BL.hPut stdout outputBytes
