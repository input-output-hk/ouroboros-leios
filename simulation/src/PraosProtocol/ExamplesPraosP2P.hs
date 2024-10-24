{-# LANGUAGE GADTs #-}
{-# LANGUAGE NamedFieldPuns #-}

module PraosProtocol.ExamplesPraosP2P where

import qualified Data.ByteString.Char8 as BS8
import Data.Functor.Contravariant (Contravariant (contramap))
import System.Random (mkStdGen)

import ChanDriver
import Network.TypedProtocol
import P2P (P2PTopographyCharacteristics (..), genArbitraryP2PTopography)
import PraosProtocol.BlockFetch
import PraosProtocol.BlockGeneration (PacketGenerationPattern (..))
import PraosProtocol.Common (BlockHeader)
import PraosProtocol.Common.Chain (Chain (Genesis))
import PraosProtocol.PraosNode
import PraosProtocol.SimPraosP2P
import PraosProtocol.VizSimPraos (PraosVizConfig (..), blockHeaderColor, examplesPraosSimVizConfig, praosSimVizModel)
import PraosProtocol.VizSimPraosP2P
import SimTCPLinks (kilobytes, mkTcpConnProps)
import SimTypes
import Viz

example1 :: Vizualisation
example1 =
  slowmoVizualisation 0.1 $
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
  model = praosSimVizModel trace
   where
    trace =
      tracePraosP2P
        rng0
        p2pTopography
        (\latency -> mkTcpConnProps latency (kilobytes 1000))
        ( \slotConfig nid rng ->
            PraosNodeConfig
              { -- blockProcessingDelay = const 0.1 -- 100ms
                blockGeneration =
                  PoissonGenerationPattern
                    (kilobytes 96)
                    rng
                    -- average seconds between blocks:
                    (0.2 * fromIntegral p2pNumNodes)
              , slotConfig
              , blockMarker = BS8.pack $ show nid ++ ": "
              , chain = Genesis
              }
        )

  p2pTopography =
    genArbitraryP2PTopography p2pTopographyCharacteristics rng0

  rng0 = mkStdGen 4 -- TODO: make a param
  p2pNumNodes = 100
  p2pTopographyCharacteristics =
    P2PTopographyCharacteristics
      { p2pWorldShape =
          WorldShape
            { worldDimensions = (0.600, 0.300)
            , worldIsCylinder = True
            }
      , p2pNumNodes
      , p2pNodeLinksClose = 5
      , p2pNodeLinksRandom = 5
      }

example2 :: Vizualisation
example2 =
  slowmoVizualisation 0.2 $
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
              { -- blockProcessingDelay = const 0.1 -- 100ms
                blockGeneration =
                  PoissonGenerationPattern
                    (kilobytes 96)
                    rng
                    -- average seconds between blocks:
                    (0.5 * fromIntegral p2pNumNodes)
              , slotConfig
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
  testNodeMessageColor = blockHeaderColor
