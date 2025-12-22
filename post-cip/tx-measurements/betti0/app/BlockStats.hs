{-# LANGUAGE TupleSections #-}


module Main where


import Control.Monad (forM_, when)
import Control.Monad.ST (ST, runST)
import Data.Array.ST (STUArray, newArray, readArray, writeArray)
import Data.Function (on)
import Data.List (groupBy, intercalate)

import qualified Data.ByteString.Lazy as LBS
import qualified Data.ByteString.Lazy.Char8 as LBS8
import qualified Data.Map as M
import qualified Data.Set as S


type TxId = Int

type SlotNo = Int

type Lifetime = Int


adjacencyGraph :: [((TxId, TxId), (SlotNo, Lifetime))] -> M.Map TxId (S.Set TxId)
adjacencyGraph edges =
  foldl (
    \acc ((u, v), (_, w)) ->
      M.insertWith (<>) u (if w == 0 then S.singleton v else mempty) acc
  ) mempty edges
    

computeSpan :: M.Map TxId (S.Set TxId) -> Int
computeSpan adjMap
    | M.null adjMap = 0
    | otherwise     = maximum $ M.elems memo
  where
    sources = M.keysSet adjMap
    destinations = S.unions (M.elems adjMap)
    allVertices = S.toList (S.union sources destinations)
    memo :: M.Map TxId Int
    memo = M.fromList [ (v, dist v) | v <- allVertices ]
    dist :: TxId -> Int
    dist v =
        case M.lookup v adjMap of
            Nothing -> 1
            Just neighbors ->
                if S.null neighbors
                    then 1
                    else 1 + maximum [ memo M.! n | n <- S.toList neighbors ]


computeMaxAntichain :: M.Map TxId (S.Set TxId) -> Int
computeMaxAntichain adjMap =
    let 
        sources = M.keysSet adjMap
        destinations = S.unions (M.elems adjMap)
        allVertices = S.toList (S.union sources destinations)
        numVertices = length allVertices
        vToInt = M.fromList $ zip allVertices [0..]
        graphInt :: [[Int]]
        graphInt = map getNeighbors allVertices
          where
            getNeighbors v = case M.lookup v adjMap of
                Nothing -> []
                Just s  -> [ vToInt M.! n | n <- S.toList s ]
    in 
        numVertices - maxBipartiteMatching numVertices graphInt


maxBipartiteMatching :: Int -> [[Int]] -> Int
maxBipartiteMatching n adjList = runST $ do
    match <- newArray (0, n - 1) (-1) :: ST s (STUArray s Int Int)
    let solve = do
            countRef <- newArray (0, 0) 0 :: ST s (STUArray s Int Int)
            forM_ [0 .. n - 1] $ \u -> do
                vis <- newArray (0, n - 1) False :: ST s (STUArray s Int Bool)
                found <- dfs u vis match
                when found $ do
                    c <- readArray countRef 0
                    writeArray countRef 0 (c + 1)
            readArray countRef 0
    solve
  where
    dfs :: Int -> STUArray s Int Bool -> STUArray s Int Int -> ST s Bool
    dfs u vis match = do
        let neighbors = adjList !! u
        recNeighbors neighbors
      where
        recNeighbors [] = pure False
        recNeighbors (v:vs) = do
            seen <- readArray vis v
            if seen
                then recNeighbors vs
                else do
                    writeArray vis v True
                    currMatch <- readArray match v
                    isAugmenting <- if currMatch == -1 
                                    then pure True 
                                    else dfs currMatch vis match
                    if isAugmenting
                        then do
                            writeArray match v u
                            pure True
                        else recNeighbors vs


main :: IO ()
main = do
  let parse :: [String] -> ((TxId, TxId), (SlotNo, Lifetime))
      parse [_, tc, ts, _, _, bc, bs] = ((read tc, read ts), (read bc, if bs == "" then -1 else read bs - read bc))
      parse _ = error "parse failed"
  rows <-
    groupBy ((==) `on` (fst . snd))
      . fmap (parse . fmap LBS8.unpack . LBS8.split '\t')
      . drop 1
      . LBS8.lines
      <$> LBS.getContents
  putStrLn "Block no\tTx count\tSpan\tAntichain"
  forM_ rows
    $ \block ->
      let blockNo = minimum $ fst . snd <$> block
          blockGraph = adjacencyGraph block
          txCount = M.size blockGraph
          spanLength = computeSpan blockGraph
          antichainLength = computeMaxAntichain blockGraph
      in
        putStrLn $ intercalate "\t" [show blockNo, show txCount, show spanLength, show antichainLength]

