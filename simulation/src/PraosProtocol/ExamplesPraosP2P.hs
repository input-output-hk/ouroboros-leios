{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE NamedFieldPuns #-}

module PraosProtocol.ExamplesPraosP2P where

import Data.Aeson
import qualified Data.ByteString.Char8 as BS8
import Data.Functor.Contravariant (Contravariant (contramap))
import qualified Data.Map.Strict as Map
import System.Random (StdGen, mkStdGen)

import ChanDriver
import Data.Coerce (coerce)
import Data.List (foldl')
import GHC.Generics
import Network.TypedProtocol
import P2P (P2PTopography (p2pNodes), P2PTopographyCharacteristics (..), genArbitraryP2PTopography)
import PraosProtocol.BlockFetch
import PraosProtocol.BlockGeneration (PacketGenerationPattern (..))
import PraosProtocol.Common
import PraosProtocol.Common.Chain (Chain (Genesis))
import PraosProtocol.PraosNode
import PraosProtocol.SimPraos
import PraosProtocol.SimPraosP2P
import PraosProtocol.VizSimPraos (DiffusionLatencyMap, PraosVizConfig (..), accumDiffusionLatency, examplesPraosSimVizConfig, praosSimVizModel)
import PraosProtocol.VizSimPraosP2P
import SimTCPLinks (mkTcpConnProps)
import SimTypes
import System.IO
import Viz
import VizSim (SimVizModel (SimVizModel))

example1 :: Vizualisation
example1 =
  Viz model $
    LayoutAbove
      [ layoutLabelTime
      , LayoutBeside
          [ LayoutReqSize 1200 1000 $
              Layout $
                praosP2PSimVizRender config
          , LayoutBeside
              [ LayoutAbove
                  [ LayoutReqSize 350 300 $
                      Layout $
                        chartDiffusionLatency config
                  , LayoutReqSize 350 300 $
                      Layout $
                        chartDiffusionImperfection
                          p2pTopography
                          0.1
                          (96 / 1000)
                          config
                  ]
              , LayoutAbove
                  [ LayoutReqSize 350 300 $
                      Layout chartBandwidth
                  , LayoutReqSize 350 300 $
                      Layout chartLinkUtilisation
                  ]
              ]
          ]
      ]
 where
  model = praosSimVizModel $ example1Trace rng0 p2pTopography
  p2pTopography = genArbitraryP2PTopography p2pTopographyCharacteristics rng0
  p2pTopographyCharacteristics =
    P2PTopographyCharacteristics
      { p2pWorldShape =
          WorldShape
            { worldDimensions = (0.600, 0.300)
            , worldIsCylinder = True
            }
      , p2pNumNodes = 100
      , p2pNodeLinksClose = 5
      , p2pNodeLinksRandom = 5
      }
  rng0 = mkStdGen 4 -- TODO make a param.

data DiffusionEntry = DiffusionEntry
  { hash :: Int
  , node_id :: Int
  , created :: DiffTime
  , arrivals :: [DiffTime]
  }
  deriving (Generic, ToJSON)

data DiffusionData = DiffusionData
  { topography :: String
  , entries :: [DiffusionEntry]
  }
  deriving (Generic, ToJSON)

diffusionSampleModel :: P2PTopographyCharacteristics -> FilePath -> SampleModel PraosEvent DiffusionLatencyMap
diffusionSampleModel p2pTopographyCharacteristics fp = SampleModel Map.empty accumDiffusionLatency render
 where
  render result = do
    encodeFile fp $
      DiffusionData
        { topography = show p2pTopographyCharacteristics
        , entries =
            [ DiffusionEntry
              { hash = coerce hash'
              , node_id = coerce i
              , created = coerce t
              , arrivals = coerce ts
              }
            | (hash', (_, i, t, ts)) <- Map.toList result
            ]
        }

-- | Diffusion example with 1000 nodes.
example1000Diffusion ::
  -- | number of links (used both for close and random)
  Int ->
  -- | when to stop simulation.
  Time ->
  -- | file to write data to.
  FilePath ->
  IO ()
example1000Diffusion nlinks stop fp =
  runSampleModel (diffusionSampleModel p2pTopographyCharacteristics fp) stop $
    example1Trace rng p2pTopography
 where
  rng = mkStdGen 42
  p2pTopography = genArbitraryP2PTopography p2pTopographyCharacteristics rng
  p2pTopographyCharacteristics =
    P2PTopographyCharacteristics
      { p2pWorldShape =
          WorldShape
            { worldDimensions = (0.600, 0.300)
            , worldIsCylinder = True
            }
      , p2pNumNodes = 1000
      , p2pNodeLinksClose = nlinks
      , p2pNodeLinksRandom = nlinks
      }

data SampleModel event state = SampleModel
  { initState :: state
  , accumState :: Time -> event -> state -> state
  , renderState :: state -> IO ()
  }

runSampleModel ::
  SampleModel event state ->
  Time ->
  [(Time, event)] ->
  IO ()
runSampleModel (SampleModel s0 accum render) stop = go . flip SimVizModel s0 . takeWhile (\(t, _) -> t <= stop)
 where
  go m = case stepSimViz 1000 m of
    m'@(SimVizModel ((now, _) : _) _) -> do
      putStrLn $ "time reached: " ++ show now
      hFlush stdout
      go m'
    (SimVizModel [] s) -> do
      putStrLn $ "done."
      render s
  stepSimViz n (SimVizModel es s) = case splitAt n es of
    (before, after) -> SimVizModel after (foldl' (\x (t, e) -> accum t e x) s before)

example1Trace :: StdGen -> P2P.P2PTopography -> PraosTrace
example1Trace rng0 p2pTopography =
  tracePraosP2P
    rng0
    p2pTopography
    (\latency -> mkTcpConnProps latency (kilobytes 1000))
    ( \slotConfig nid rng ->
        PraosNodeConfig
          { blockGeneration =
              PoissonGenerationPattern
                (kilobytes 96)
                rng
                -- average seconds between blocks:
                (5 * fromIntegral p2pNumNodes)
          , praosConfig =
              PraosConfig
                { slotConfig
                , blockValidationDelay = const 0.1 -- 100ms
                }
          , blockMarker = BS8.pack $ show nid ++ ": "
          , chain = Genesis
          }
    )
 where
  p2pNumNodes = Map.size $ p2pNodes p2pTopography

example2 :: Vizualisation
example2 =
  --  slowmoVizualisation 0.2 $
  Viz (pairVizModel model1 model2) $
    LayoutAbove
      [ layoutLabel 18 "Flat vs cylindrical world topology"
      , LayoutReqSize 0 40 $
          layoutLabel 10 $
            "Left side is a flat rectangular world.\n"
              ++ "Right is a cylindrical world, i.e. the east and "
              ++ "west edges are connected."
      , layoutLabelTime
      , LayoutBeside
          [ contramap fst
              <$> LayoutAbove
                [ LayoutReqSize 900 600 $
                    Layout $
                      praosP2PSimVizRender config
                , LayoutBeside
                    [ LayoutReqSize 350 300 $
                        Layout $
                          chartDiffusionLatency config
                    , LayoutReqSize 350 300 $
                        Layout
                          chartLinkUtilisation
                    ]
                ]
          , contramap snd
              <$> LayoutAbove
                [ LayoutReqSize 900 600 $
                    Layout $
                      praosP2PSimVizRender config
                , LayoutBeside
                    [ LayoutReqSize 350 300 $
                        Layout $
                          chartDiffusionLatency config
                    , LayoutReqSize 350 300 $
                        Layout
                          chartLinkUtilisation
                    ]
                ]
          ]
      ]
 where
  model1 =
    model
      p2pTopographyCharacteristicsCommon
        { p2pWorldShape =
            p2pWorldShape
              { worldIsCylinder = False
              }
        }
  model2 = model p2pTopographyCharacteristicsCommon

  model p2pTopographyCharacteristics =
    praosSimVizModel trace
   where
    trace =
      tracePraosP2P
        rng0
        p2pTopography
        (\latency -> mkTcpConnProps latency (kilobytes 1000))
        ( \slotConfig nid rng ->
            PraosNodeConfig
              { blockGeneration =
                  PoissonGenerationPattern
                    (kilobytes 96)
                    rng
                    -- average seconds between blocks:
                    (5 * fromIntegral p2pNumNodes)
              , praosConfig =
                  PraosConfig
                    { slotConfig
                    , blockValidationDelay = const 0.1 -- 100ms
                    }
              , chain = Genesis
              , blockMarker = BS8.pack $ show nid ++ ": "
              }
        )
    p2pTopography =
      genArbitraryP2PTopography p2pTopographyCharacteristics rng0

  rng0 = mkStdGen 4 -- TODO: make a param
  p2pNumNodes = 100
  p2pWorldShape =
    WorldShape
      { worldDimensions = (0.600, 0.300)
      , worldIsCylinder = True
      }
  p2pTopographyCharacteristicsCommon =
    P2PTopographyCharacteristics
      { p2pWorldShape
      , p2pNumNodes
      , p2pNodeLinksClose = 5
      , p2pNodeLinksRandom = 5
      }

config :: PraosP2PSimVizConfig
config =
  PraosP2PSimVizConfig
    { nodeMessageColor = testNodeMessageColor
    , ptclMessageColor = testPtclMessageColor
    }
 where
  testPtclMessageColor ::
    PraosMessage ->
    Maybe (Double, Double, Double)
  testPtclMessageColor msg =
    case msg of
      PraosMessage (Right bmsg@(ProtocolMessage (SomeMessage MsgBlock{}))) ->
        Just (blockFetchMessageColor examplesPraosSimVizConfig bmsg)
      _ -> Nothing

  testNodeMessageColor :: BlockHeader -> (Double, Double, Double)
  testNodeMessageColor = blockHeaderColorAsBody
