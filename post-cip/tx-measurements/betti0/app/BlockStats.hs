{-# LANGUAGE TupleSections #-}


module Main where


import Control.Monad (forM_)
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
    

computeGraphStats :: M.Map TxId (S.Set TxId) -> (Int, Int)
computeGraphStats adjMap
    | M.null adjMap = (0, 0)
    | otherwise     = (M.size adjMap, maximum (M.elems memo))
  where
    sources = M.keysSet adjMap
    destinations = S.unions (M.elems adjMap)
    allVertices = S.toList (S.union sources destinations)
    memo :: M.Map TxId Int
    memo = M.fromList [ (v, dist v) | v <- allVertices ]
    dist :: TxId -> Int
    dist v =
        case M.lookup v adjMap of
            Nothing -> 1 -- Node is a leaf (not a key in the map)
            Just neighbors ->
                if S.null neighbors
                    then 1
                    else 1 + maximum [ memo M.! n | n <- S.toList neighbors ]


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
  putStrLn "Block no\tTx count\tSpan"
  forM_ rows
    $ \block ->
      let blockNo = fst . snd $ head block
          blockGraph = adjacencyGraph block
          (txCount, spanLength) = computeGraphStats blockGraph
      in
        putStrLn $ intercalate "\t" [show blockNo, show txCount, show spanLength]

