{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE NamedFieldPuns #-}

module P2P where

import Data.List
import qualified Data.Map.Strict as Map
import           Data.Map.Strict (Map)
import Data.Function (on)
import Data.Graph as Graph
import Data.Array.ST as Array
import Data.Array.Unboxed as Array

import Control.Monad
import Control.Monad.ST
import Control.Monad.Class.MonadTime.SI (DiffTime)
import qualified System.Random as Random
import           System.Random (StdGen)

import SimTCPLinks (NodeId(..)) -- TODO move this definition to some common module


data P2PTopography =
     P2PTopography {
       p2pNodes :: Map NodeId Point,
       p2pLinks :: Map (NodeId, NodeId) Latency
     }
  deriving (Show)

type Point = (Double,Double)
type Latency = DiffTime

data P2PTopographyCharacteristics =
     P2PTopographyCharacteristics {
       -- | Size of the world (in seconds): (Circumference, pole-to-pole)
       p2pWorldDimensions :: (DiffTime, DiffTime),

       -- ^ Number of nodes, e.g. 100, 1000, 10,000
       p2pNumNodes        :: Int,

       -- ^ Per-node upstream links picked as close peers, e.g. 5 of 10 total
       p2pNodeLinksClose  :: Int,

       -- ^ Per-node upstream links picked as random peers, e.g. 5 of 10 total
       p2pNodeLinksRandom :: Int
     }
  deriving (Show)


-- | Strategy for creating an arbitrary P2P network:
--
-- * The world is a 2-d rectangle, with the topologoy of a cylinder: connected
--   around the middle but not over the poles. This means the shortest link between
--   two nodes can cros the "date line".
-- * Scatter nodes randomly on the rectangle
-- * All links will be directed
-- * For a given uniform in-degree (e.g. 10-20) pick upstream peers by the
--   "close + random" strategy, e.g. 50%:50%, or 40%:60%
-- * For close peers, pick the first N peers by min distance.
-- * For random peers, pick randomly (perhaps avoiding ones already picked, or self)
-- * The latency of each link will be chosen based on the shortest distance
--   between the nodes: connecting over the "date line" if necessary.
--
genArbitraryP2PTopography :: P2PTopographyCharacteristics
                          -> StdGen
                          -> P2PTopography
genArbitraryP2PTopography P2PTopographyCharacteristics{
                            p2pWorldDimensions  = (widthSeconds, heightSeconds),
                            p2pNumNodes,
                            p2pNodeLinksClose,
                            p2pNodeLinksRandom
                          } rng0 =
    P2PTopography {
      p2pNodes = nodePositions,
      p2pLinks = nodeLinks
    }
  where
    nodes :: [NodeId]
    nodes = [ NodeId n | n <- [0..p2pNumNodes-1] ]

    (rngNodes, rngLinks) = Random.split rng0

    nodePositions :: Map NodeId Point
    nodePositions =
        Map.map toNormalisedPoint nodePositionsTime

    -- map the time-based positions into positions on a unit square
    toNormalisedPoint :: (DiffTime, DiffTime) -> Point
    toNormalisedPoint = \(x,y) -> (realToFrac x / realToFrac widthSeconds,
                                   realToFrac y / realToFrac heightSeconds)

    nodePositionsTime :: Map NodeId (DiffTime, DiffTime)
    nodePositionsTime =
        Map.fromList $ snd $ mapAccumL genNodePos rngNodes nodes
      where
        genNodePos :: StdGen -> NodeId -> (StdGen, (NodeId, (DiffTime, DiffTime)))
        genNodePos rng nodeid =
            (rng'', (nodeid, (realToFrac x, realToFrac y)))
          where
            x, y :: Double
            (x, !rng')  = Random.uniformR (0, realToFrac widthSeconds)  rng
            (y, !rng'') = Random.uniformR (0, realToFrac heightSeconds) rng'

    linkDistances :: Map (Int, Int) DiffTime
    linkDistances =
      Map.fromList
        [ ((n1, n2), distance)
        | NodeId n1 <- nodes
        , NodeId n2 <- nodes
        , n1 <= n2
        , let Just (x1,y1) = Map.lookup (NodeId n1) nodePositionsTime
              Just (x2,y2) = Map.lookup (NodeId n2) nodePositionsTime

              dx, dy :: Double
              dx = realToFrac (x1-x2)
              dy = realToFrac (y1-y2)

              distance :: DiffTime
              distance =
                realToFrac $
                  sqrt (dx*dx + dy*dy)
              --TODO: shortest path across date line!s
        ]

    linkDistance :: NodeId -> NodeId -> DiffTime
    linkDistance (NodeId n1) (NodeId n2)
      | n1 <= n2  = let Just d = Map.lookup (n1, n2) linkDistances in d
      | otherwise = linkDistance (NodeId n2) (NodeId n1)

    nodeLinks :: Map (NodeId, NodeId) Latency
    nodeLinks =
      Map.fromList
        [ ((nid,nid'), latency)
        | (nid, rng) <- zip nodes (unfoldr (Just . Random.split) rngLinks)
        , nid' <- pickNodeLinksClose  nid
               ++ pickNodeLinksRandom nid rng
        , let latency = linkDistance nid nid'
        ]

    pickNodeLinksClose :: NodeId -> [NodeId]
    pickNodeLinksClose nid =
        take p2pNodeLinksClose
      $ map fst
      $ sortBy (compare `on` snd)
        [ (nid', linkDistance nid nid')
        | nid' <- nodes
        , nid' /= nid
        ]

    pickNodeLinksRandom :: NodeId -> StdGen -> [NodeId]
    pickNodeLinksRandom nid rng =
        take p2pNodeLinksRandom
        [ NodeId nid'
        | nid' <- Random.randomRs (0, p2pNumNodes-1) rng
        , nid /= NodeId nid' ]

exampleTopographyCharacteristics1 :: P2PTopographyCharacteristics
exampleTopographyCharacteristics1 =
  P2PTopographyCharacteristics {
    p2pWorldDimensions  = (0.600, 0.300),
    p2pNumNodes         = 50,
    p2pNodeLinksClose   = 5,
    p2pNodeLinksRandom  = 5
  }


data P2PIdealDiffusionTimes =
     P2PIdealDiffusionTimes !Graph !(UArray (Vertex, Vertex) Double)

-- | The timeseries of the ideal\/perfect diffusion times from the given node
-- to all other nodes.
--
p2pGraphIdealDiffusionTimesFromNode
  :: P2PIdealDiffusionTimes
  -> NodeId -- ^ From this node to all other nodes
  -> [DiffTime]
p2pGraphIdealDiffusionTimesFromNode (P2PIdealDiffusionTimes g latencies)
                                    (NodeId nid) =
    sort [ realToFrac (latencies ! (nid, nid'))
         | nid' <- range (bounds g) ]


-- | Compute the ideal\/perfect diffusion times between all nodes.
--
-- This depends on the p2p graph and on the processing and communication times.
-- The communication time must be provided as a function from the one-way link
-- latency. For example, a protocol that involved 3 one-way ballistic message
-- exchanges (for hypothetical zero-sized messages) would be three times the
-- latency. This function should also take account of serialisation and
-- processing delays if approproate.
--
p2pGraphIdealDiffusionTimes
  :: P2PTopography
  -> (NodeId -> DiffTime)  -- ^ Per node processing time
  -> (NodeId -> NodeId -> DiffTime -> DiffTime)
                           -- ^ Communication latency between nodes,
                           -- given the link one-way link latency
  -> P2PIdealDiffusionTimes
p2pGraphIdealDiffusionTimes P2PTopography { p2pNodes, p2pLinks }
                            processingDelay communicationDelay =
    P2PIdealDiffusionTimes p2pGraph $
      allPairsMinWeights
        p2pGraph
        (\(a,b) -> let linkLatency, msgLatency :: DiffTime
                       linkLatency = p2pLinks Map.! (NodeId a, NodeId b)
                       msgLatency  = communicationDelay
                                       (NodeId a) (NodeId b) linkLatency
                    in realToFrac msgLatency
        )
        (realToFrac . processingDelay . NodeId)
  where
    p2pGraph :: Graph
    p2pGraph =
      Graph.buildG
        (0, Map.size p2pNodes - 1)
         [ (a, b) | (NodeId a, NodeId b) <- Map.keys p2pLinks ]

allPairsMinWeights :: Graph
                   -> (Edge   -> Double)
                   -> (Vertex -> Double)
                   -> UArray (Vertex, Vertex) Double
allPairsMinWeights g edgeWeight vertexWeight =
    runSTUArray floydWarshall
  where
    floydWarshall :: ST s (STUArray s (Int, Int) Double)
    floydWarshall = do
      let (_, n)   = bounds g
          infinity = 1/0 :: Double
      arr <- newArray ((0,0), (n,n)) infinity
      sequence_ [ writeArray arr e (edgeWeight e) | e <- edges g ]
      sequence_ [ writeArray arr (v,v) 0 | v <- [0..n] ]
      sequence_ [ do w_ik <- readArray arr (i,k)
                     w_kj <- readArray arr (k,j)
                     w_ij <- readArray arr (i,j)
                     let !w_ikj = w_ik + w_kj + vertexWeight k
                     when (w_ij > w_ikj) $
                       writeArray arr (i,j) w_ikj
                | k <- [0..n]
                , i <- [0..n]
                , j <- [0..n]
                ]
      return arr

