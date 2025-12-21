{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE RecordWildCards #-}


module Main where


import Control.DeepSeq (NFData)
import Control.Monad (forM_, when, zipWithM_)
import Control.Monad.ST (ST, runST)
import Control.Parallel.Strategies (using, parBuffer, rdeepseq)
import Data.Array.ST (STUArray, newArray, readArray, writeArray)
import Data.Function (on)
import Data.List (intercalate, nub, sortBy, nub)
import GHC.Generics (Generic)
import System.Environment (getArgs)
import System.IO (IOMode(WriteMode), hClose, hPutStrLn, openFile, stderr)

import qualified Data.Map.Strict as M
import qualified Data.ByteString.Lazy as BL
import qualified Data.ByteString.Lazy.Char8 as BL8
import qualified Data.Vector as V


tab :: String
tab = "\t"


type TxId = Int

type Weight = Int

data Record =
  Record
  {
    utxoId12 :: String
  , txCreateId :: TxId
  , txSpendId :: TxId
  , lifetimeSlots :: Weight
  , lifetimeBlocks :: Weight
  }
  deriving (Eq, Generic, Ord, NFData, Read, Show)

readGZippedTSV' :: (Record -> Bool) -> FilePath -> IO [Record]
readGZippedTSV' wFilter path = do
  rawContent <- BL.readFile path
  let rows = BL8.lines rawContent
  let parse :: [String] -> Record
      parse [ut, tc, ts, sc, ss, bc, bs] =
        Record
          (take 12 ut)
          (read tc)
          (read ts)
          (read ss - read sc)
          (read bs - read bc)
      parse x = error $ show x
  pure
    . filter wFilter
    . fmap (parse . fmap BL8.unpack)
    . filter ((/= mempty) . (!! 2))
    . fmap (BL8.split '\t')
    $ drop 1 rows

chunkSize :: Int
chunkSize = 10000 -- Adjust based on memory. 10k-50k is usually the sweet spot.

readGZippedTSV :: (Record -> Bool) -> FilePath -> IO [Record]
readGZippedTSV wFilter path = do
    rawContent <- BL.readFile path
    let rows = drop 1 $ BL8.lines rawContent
    let chunks = chunkLines chunkSize rows
    -- CHANGE 1: The worker now SORTS the chunk before returning it
    let processAndSort lines' = 
            let parsed = processChunk wFilter lines' -- Use previous logic
            in sortBy (compare `on` lifetimeSlots) parsed     -- Sort by 'rTC' (or your weight field)
    -- CHANGE 2: Map the sorting worker over chunks
    let sortedChunks = map processAndSort chunks
    -- CHANGE 3: Evaluate chunks in parallel
    let evaluatedChunks = sortedChunks `using` parBuffer 8 rdeepseq
    -- CHANGE 4: Merge the sorted chunks instead of just concatenating
    -- This happens lazily in the main thread, but is very fast.
    let finalStream = mergeAll (compare `on` lifetimeSlots) evaluatedChunks
    return finalStream

-- Helper: Process a single chunk of lines (Sequential work for one core)
processChunk :: (Record -> Bool) -> [BL.ByteString] -> [Record]
processChunk wFilter lines' =
    let 
        -- Optimization: define parse locally to capture closure if needed
        parse parts = 
             let ut = parts !! 0
                 tc = parts !! 1
                 ts = parts !! 2
                 sc = parts !! 3
                 ss = parts !! 4
                 bc = parts !! 5
                 bs = parts !! 6
                 -- Helper to unpack only when necessary
                 sRead = read . BL8.unpack 
             in
             Record 
                (take 12 (BL8.unpack ut))
                (sRead tc)
                (sRead ts)
                (sRead ss - sRead sc)
                (sRead bs - sRead bc)
        processLine line = 
            let parts = BL8.split '\t' line
            in if length parts >= 7 && (parts !! 2) /= mempty 
               then 
                   let rec = parse parts
                   in if wFilter rec then [rec] else [] -- List comprehension style filter
               else []
    in concatMap processLine lines'

-- Helper: Split list into chunks
chunkLines :: Int -> [a] -> [[a]]
chunkLines _ [] = []
chunkLines n xs = 
    let (h, t) = splitAt n xs 
    in h : chunkLines n t

-- 1. Helper: Efficient Merge of two SORTED lists
--    (Standard Haskell does not export a merge function for lists)
merge :: (a -> a -> Ordering) -> [a] -> [a] -> [a]
merge _ xs [] = xs
merge _ [] ys = ys
merge cmp (x:xs) (y:ys) = 
  case cmp x y of
    GT -> y : merge cmp (x:xs) ys -- y is smaller, take y
    _  -> x : merge cmp xs (y:ys) -- x is smaller or equal, take x

-- 2. Helper: Pairwise Merge (Tournament Tree)
--    Merges a list of sorted lists into one single sorted list.
--    We merge pairs (L1+L2, L3+L4) repeatedly to keep the stack depth low.
mergeAll :: (a -> a -> Ordering) -> [[a]] -> [a]
mergeAll _ [] = []
mergeAll _ [x] = x
mergeAll cmp lists = mergeAll cmp (pairwise lists)
  where
    pairwise [] = []
    pairwise [x] = [x]
    pairwise (x:y:zs) = merge cmp x y : pairwise zs


data Edge =
  Edge
  {
    u :: Int
  , v :: Int
  , w :: Weight
  }
  deriving (Show)

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
      pure True -- Merged successfully
    else pure False -- Already in same component

-- 3. MAIN ALGORITHM: Compute Betti-0 Curve
computeBetti0 :: Int -> [Edge] -> [(Weight, Int)]
computeBetti0 numNodes sortedEdges = runST $ do
  -- Initialize Union-Find
  parent <- newArray (0, numNodes - 1) 0 :: ST s (STUArray s Int Int)
  rank   <- newArray (0, numNodes - 1) 0 :: ST s (STUArray s Int Int)
  -- Initialize parent array so each node points to itself
  forM_ [0 .. numNodes - 1] $ \i -> writeArray parent i i
  -- Iterate through edges and track Betti-0
  -- Using a recursive helper to accumulate results
  let go [] _ = pure mempty
      go (e:es) currentCount = do
          merged <- union parent rank (u e) (v e)
          let newCount = if merged then currentCount - 1 else currentCount
          -- Look ahead to handle edges with identical weights
          -- We only emit a data point when the weight actually changes
          case es of
            (nextE:_) | w nextE == w e -> go es newCount
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
    forM_ [0 .. numNodes - 1] $ \i -> writeArray parent i i
    let go [] _ = pure mempty
        go (e:es) _ = do -- We don't need to track 'count' anymore
            _ <- union parent rank (u e) (v e) -- Ignore boolean result
            case es of
                (nextE:_) | w nextE == w e -> go es ()
                _                          -> do
                                -- SNAPSHOT: This is the expensive part (O(N))
                                currentRoots <- getSnapshot parent numNodes
                                tailRes <- go es ()
                                pure ((w e, currentRoots) : tailRes)
    go sortedEdges ()


blockEdge :: M.Map TxId Int -> Record -> Edge
blockEdge vertexMap Record{..} = Edge (vertexMap M.! txCreateId) (vertexMap M.! txSpendId) lifetimeBlocks

slotEdge :: M.Map TxId Int -> Record -> Edge
slotEdge vertexMap Record{..} = Edge (vertexMap M.! txCreateId) (vertexMap M.! txSpendId) lifetimeSlots


main :: IO ()
main =
  do
    [wType, wMax', infile, outfile] <- getArgs
    let wMax = read wMax'
    let wFilter :: Record -> Bool
        wFilter =
          case wType of
            "block" -> (<= wMax) . lifetimeBlocks
            "slot" -> (<= wMax) . lifetimeSlots
            _ -> const True
    rows <- readGZippedTSV wFilter infile
    let vertices = V.fromList . nub $ (txCreateId <$> rows) <> (txSpendId <$> rows)
    let vertexMap = M.fromList $ zip (V.toList vertices) [0..]
    let n = V.length vertices
    let edges = blockEdge vertexMap <$> rows
    hPutStrLn stderr $ "Filter: " <> wType <> " lifetime <= " <> show wMax
    hPutStrLn stderr $ "Vertices: " <> show n
    hPutStrLn stderr $ "Edges: " <> show (length edges)
    let sortedEdges = sortBy (compare `on` w) edges
    if False
      then do
        let bettiCurve = computeBetti0 n sortedEdges
        putStrLn "Lifetime \t Betti-0"
        mapM_ (\(w, b) -> putStrLn $ intercalate tab [show w, show b]) bettiCurve
      else do
        let memberships = computeMembership n sortedEdges
        h <- openFile outfile WriteMode
        forM_ memberships
          $ \(w, components) ->
            zipWithM_
              (\i c -> hPutStrLn h $ intercalate tab [show w, show $ vertices V.! i, show c])
              [0..] components
        hClose h
        putStrLn "Lifetime \t Betti-0"
        forM_ memberships
          $ \(w, components) -> putStrLn $ intercalate tab [show w, show . length $ nub components]

