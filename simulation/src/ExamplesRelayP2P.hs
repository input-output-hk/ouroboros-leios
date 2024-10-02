{-# LANGUAGE NamedFieldPuns #-}

module ExamplesRelayP2P where

import Data.Word
import Data.Functor.Contravariant

import System.Random (mkStdGen, uniform)

import RelayProtocol
import SimTypes
import SimTCPLinks (mkTcpConnProps, kilobytes)
import SimRelay
import P2P (P2PTopographyCharacteristics(..), genArbitraryP2PTopography)
import SimRelayP2P
import Viz
import VizSimRelay (relaySimVizModel)
import VizSimRelayP2P


example1 :: Vizualisation
example1 =
    slowmoVizualisation 0.1 $
    Viz model $
      LayoutAbove
        [ layoutLabelTime
        , LayoutBeside
            [ LayoutReqSize 1200 1000 $
              Layout $ relayP2PSimVizRender config
            , LayoutBeside
                [ LayoutAbove
                    [ LayoutReqSize 350 300 $
                      Layout $ chartDiffusionLatency config
                    , LayoutReqSize 350 300 $
                      Layout $ chartDiffusionImperfection
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
    model = relaySimVizModel trace
      where
        trace =
          traceRelayP2P
            rng0
            p2pTopography
            (\latency -> mkTcpConnProps latency (kilobytes 1000))
            (\rng ->
             RelayNodeConfig {
               blockProcessingDelay = const 0.1, -- 100ms
               blockGeneration      =
                 PoissonGenerationPattern
                  (kilobytes 96)
                  rng
                  -- average seconds between blocks:
                  (0.2 * fromIntegral p2pNumNodes)
                  5.0
             })

    p2pTopography =
      genArbitraryP2PTopography p2pTopographyCharacteristics rng0

    rng0 = mkStdGen 4 --TODO: make a param

    p2pNumNodes         = 100
    p2pTopographyCharacteristics =
      P2PTopographyCharacteristics {
        p2pWorldShape       = WorldShape {
                                worldDimensions = (0.600, 0.300),
                                worldIsCylinder = True
                              },
        p2pNumNodes,
        p2pNodeLinksClose   = 5,
        p2pNodeLinksRandom  = 5
      }


example2 :: Vizualisation
example2 =
    slowmoVizualisation 0.2 $
    Viz (pairVizModel model1 model2) $
      LayoutAbove
        [ layoutLabel 18 "Flat vs cylindrical world topology"
        , LayoutReqSize 0 40 $
          layoutLabel 10 $ "Left side is a flat rectangular world.\n"
                        ++ "Right is a cylindrical world, i.e. the east and "
                        ++ "west edges are connected."
        , layoutLabelTime
        , LayoutBeside
            [ fmap (contramap fst) $
              LayoutAbove
                [ LayoutReqSize 900 600 $
                  Layout $ relayP2PSimVizRender config
                , LayoutBeside
                    [ LayoutReqSize 350 300 $
                      Layout $ chartDiffusionLatency config
                    , LayoutReqSize 350 300 $
                      Layout $ chartLinkUtilisation
                    ]
                ]
            , fmap (contramap snd) $
              LayoutAbove
                [ LayoutReqSize 900 600 $
                  Layout $ relayP2PSimVizRender config
                , LayoutBeside
                    [ LayoutReqSize 350 300 $
                      Layout $ chartDiffusionLatency config
                    , LayoutReqSize 350 300 $
                      Layout $ chartLinkUtilisation
                    ]
                ]
            ]
        ]
  where
    model1 = model p2pTopographyCharacteristicsCommon {
                     p2pWorldShape =
                       p2pWorldShape {
                         worldIsCylinder = False
                       }
                   }
    model2 = model p2pTopographyCharacteristicsCommon

    model p2pTopographyCharacteristics =
        relaySimVizModel trace
      where
        trace =
          traceRelayP2P
            rng0
            p2pTopography
            (\latency -> mkTcpConnProps latency (kilobytes 1000))
            (\rng ->
             RelayNodeConfig {
               blockProcessingDelay = const 0.1, -- 100ms
               blockGeneration      =
                 PoissonGenerationPattern
                  (kilobytes 96)
                  rng
                  -- average seconds between blocks:
                  (0.5 * fromIntegral p2pNumNodes)
                  10.0
             })
        p2pTopography =
          genArbitraryP2PTopography p2pTopographyCharacteristics rng0

    rng0 = mkStdGen 4 --TODO: make a param

    p2pNumNodes   = 100
    p2pWorldShape = WorldShape {
                      worldDimensions = (0.600, 0.300),
                      worldIsCylinder = True
                    }
    p2pTopographyCharacteristicsCommon =
      P2PTopographyCharacteristics {
        p2pWorldShape,
        p2pNumNodes,
        p2pNodeLinksClose   = 5,
        p2pNodeLinksRandom  = 5
      }

config :: RelayP2PSimVizConfig
config =
  RelayP2PSimVizConfig {
    nodeMessageColor = testNodeMessageColor,
    ptclMessageColor = testPtclMessageColor
  }
  where
    testPtclMessageColor :: TestBlockRelayMessage
                         -> Maybe (Double, Double, Double)
    testPtclMessageColor (MsgRespBlock pkt) = Just (testNodeMessageColor pkt)
    testPtclMessageColor _                  = Nothing

    testNodeMessageColor :: TestBlock -> (Double, Double, Double)
    testNodeMessageColor (TestBlock (TestBlockId blkid) _ _) =
        (fromIntegral r / 256, fromIntegral g / 256, fromIntegral b / 256)
      where
        r, g, b :: Word8
        ((r,g,b), _) = uniform (mkStdGen blkid)

