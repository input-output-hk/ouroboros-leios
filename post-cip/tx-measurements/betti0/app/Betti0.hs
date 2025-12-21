{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE StrictData #-}


module Main where


import Control.Monad (forM_, when, zipWithM_)
import Control.Monad.ST (ST, runST)
import Data.Array.ST (STUArray, newArray, readArray, writeArray)
import Data.List (intercalate)
import System.Environment (getArgs)
import System.IO (IOMode(WriteMode), hClose, hPutStrLn, openFile, stderr)

import qualified Data.ByteString.Lazy as BL
import qualified Data.ByteString.Lazy.Char8 as BL8
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import qualified Data.Vector as V


tab :: String
tab = "\t"


type TxId = Int

type Weight = Int

data Edge =
  Edge
  {
    u :: Int
  , v :: Int
  , w :: Weight
  }
  deriving (Show)


readTsv :: ((Weight, Weight) -> Weight) -> Weight -> FilePath -> IO (V.Vector TxId, [Edge])
readTsv getWeight maxWeight path = do
  rawContent <- BL.readFile path
  let rows = BL8.lines rawContent
      parse :: [String] -> ((TxId, TxId), Weight)
      parse [_, tc, ts, ls, bs] = ((read tc, read ts), getWeight (read ls, read bs))
      parse x = error $ show x
      edges =
          takeWhile ((<= maxWeight) . snd)
        . fmap (parse . fmap BL8.unpack . BL8.split '\t')
        $ drop 1 rows
      vertices = V.fromList . S.toList $ S.fromList (fst . fst <$> edges) <> S.fromList (snd . fst <$> edges)
      vertexMap = M.fromList $ zip (V.toList vertices) [0..]
      reindex :: ((TxId, TxId), Weight) -> Edge 
      reindex ((tc, ts), w) = Edge (vertexMap M.! tc) (vertexMap M.! ts) w
  pure (vertices, reindex <$> edges)


find :: STUArray s Int Int -> Int -> ST s Int
find parent i = do
  p <- readArray parent i
  if p == i
    then pure i
    else do
      -- Path Compression: Point i directly to the root
      root <- find parent p
      writeArray parent i root
      pure root

union :: STUArray s Int Int -> STUArray s Int Int -> Int -> Int -> ST s Bool
union parent rank i j = do
  rootI <- find parent i
  rootJ <- find parent j
  if rootI /= rootJ
    then do
      -- Union by Rank: Attach smaller tree to larger tree
      rankI <- readArray rank rootI
      rankJ <- readArray rank rootJ
      if rankI < rankJ
        then writeArray parent rootI rootJ
        else do
          writeArray parent rootJ rootI
          when (rankI == rankJ)
            $ writeArray rank rootI (rankI + 1)
      -- Merged successfully
      pure True 
    else
      -- Already in same component
      pure False

computeBetti0 :: Int -> [Edge] -> [(Weight, Int)]
computeBetti0 numNodes sortedEdges = runST $ do
  -- Initialize Union-Find
  parent <- newArray (0, numNodes - 1) 0 :: ST s (STUArray s Int Int)
  rank   <- newArray (0, numNodes - 1) 0 :: ST s (STUArray s Int Int)
  -- Initialize parent array so each node points to itself
  forM_ [0 .. numNodes - 1]
    $ \i -> writeArray parent i i
  -- Iterate through edges and track Betti-0
  -- Using a recursive helper to accumulate results
  let go [] _ = pure mempty
      go (e:es) currentCount = do
        merged <- union parent rank (u e) (v e)
        let newCount = if merged then currentCount - 1 else currentCount
        -- Look ahead to handle edges with identical weights
        -- We only emit a data point when the weight actually changes
        case es of
          (nextE : _) | w nextE == w e -> go es newCount
          _  -> ((w e, newCount) :) <$> go es newCount
  -- Start with b0 = numNodes (everyone is isolated)
  go sortedEdges numNodes


-- Helper to get the canonical root for EVERY node
getSnapshot :: STUArray s Int Int -> Int -> ST s [Int]
getSnapshot parent numNodes = do
  -- We map 'find' over every node index [0 .. n-1]
  -- Note: This modifies the array (path compression), which is good!
  mapM (find parent) [0 .. numNodes - 1]

computeMembership :: Int -> [Edge] -> [(Weight, [Int])]
computeMembership numNodes sortedEdges = runST $ do
  parent <- newArray (0, numNodes - 1) 0 :: ST s (STUArray s Int Int)
  rank   <- newArray (0, numNodes - 1) 0 :: ST s (STUArray s Int Int)
  forM_ [0 .. numNodes - 1]
    $ \i -> writeArray parent i i
  let go [] = pure mempty
      go (e:es) = do
        _ <- union parent rank (u e) (v e) -- Ignore boolean result
        case es of
          (nextE : _) | w nextE == w e -> go es
          _ -> do
                 -- SNAPSHOT: This is the expensive part (O(N))
                 currentRoots <- getSnapshot parent numNodes
                 tailRes <- go es
                 pure ((w e, currentRoots) : tailRes)
  go sortedEdges


main :: IO ()
main = do
 [wType, wMax, infile, outfile] <- getArgs
 let maxWeight = read wMax
     getWeight :: (Weight, Weight) -> Weight
     getWeight =
       case wType of
         "slot" -> fst
         "block" -> snd
         _ -> error "invalid type"
 (vertices, edges) <- readTsv getWeight maxWeight infile
 let n = V.length vertices
 hPutStrLn stderr $ "Filter: " <> wType <> " lifetime <= " <> show maxWeight
 hPutStrLn stderr $ "Vertices: " <> show n
 hPutStrLn stderr $ "Edges: " <> show (length edges)
 if False
   then do
     let bettiCurve = computeBetti0 n edges
     putStrLn "Lifetime\tBetti-0"
     mapM_ (\(w, b) -> putStrLn $ intercalate tab [show w, show b]) bettiCurve
   else do
     let memberships = computeMembership n edges
     putStrLn "Lifetime\tBetti-0"
     h <- openFile outfile WriteMode
     forM_ memberships
       $ \(w, components) -> do
         zipWithM_
           (\i c -> hPutStrLn h $ intercalate tab [show w, show $ vertices V.! i, show c])
           [0..] components
         putStrLn $ intercalate tab [show w, show . S.size $ S.fromList components]
     hClose h

