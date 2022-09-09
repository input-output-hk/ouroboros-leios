{-# LANGUAGE NamedFieldPuns #-}

module ExamplesRelayP2P where

import Data.Word
import System.Random (mkStdGen, uniform)

import RelayProtocol
import SimTCPLinks (mkTcpConnProps, kilobytes)
import SimRelay
import P2P
import SimRelayP2P
import Viz
import VizSimRelay (relaySimVizModel)
import VizSimRelayP2P


example1 :: Vizualisation
example1 =
    slowmoVizualisation 0.1 $
    let trace =
          traceRelayP2P
            (mkStdGen 4)
            p2pTopographyCharacteristics
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
     in Viz (relaySimVizModel trace)
            (aboveVizRender
               labelTimeVizRender
              (besideVizRender
                 (relayP2PSimVizRender config p2pScreenDimensions)
                 (chartDiffusionLatency config)))
  where
    p2pScreenDimensions = (1280, 1060)
    p2pNumNodes         = 100
    p2pTopographyCharacteristics =
      P2PTopographyCharacteristics {
        p2pWorldDimensions  = (0.600, 0.300),
        p2pScreenDimensions,
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

