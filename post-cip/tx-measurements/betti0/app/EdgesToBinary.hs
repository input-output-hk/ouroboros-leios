-- File: ConvertToBin.hs
import qualified Data.ByteString.Lazy as BL
import qualified Data.ByteString.Lazy.Char8 as BL8
import qualified Data.ByteString.Builder as BB
import Data.Int (Int64)
import System.IO (stdout)

-- 1. Define the Builder for a single edge
-- This creates a 24-byte binary chunk
encodeEdge :: Int64 -> Int64 -> Double -> Double -> BB.Builder
encodeEdge u v w w' = 
    BB.int64LE u <> 
    BB.int64LE v <> 
    BB.doubleLE w <>
    BB.doubleLE w'

-- 2. Parsing logic (similar to your existing code)
processLine :: BL.ByteString -> BB.Builder
processLine line = 
    let parts = BL8.split '\t' line
        u = read (BL8.unpack (parts !! 1)) :: Int64
        v = read (BL8.unpack (parts !! 2)) :: Int64
        w = read (BL8.unpack (parts !! 3)) :: Double
        w' = read (BL8.unpack (parts !! 4)) :: Double
    in encodeEdge u v w w'

-- 3. Streaming Converter
main :: IO ()
main = do
    input <- BL.getContents
    let lines = drop 1 $ BL8.lines input -- Skip header
    
    -- Lazily map lines to binary builders
    let binaryStream = map processLine lines
    
    -- Concatenate into one massive lazy ByteString
    let outputBytes = BB.toLazyByteString (mconcat binaryStream)
    
    -- Write to Stdout (pipe this to a file)
    BL.hPut stdout outputBytes
