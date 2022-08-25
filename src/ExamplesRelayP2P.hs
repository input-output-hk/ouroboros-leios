module ExamplesRelayP2P where

import Data.Word
import System.Random (mkStdGen, uniform)

import RelayProtocol
import SimTCPLinks (mkTcpConnProps, kilobytes)
import SimRelay
import P2P
import SimRelayP2P
import Viz
import VizSimRelayP2P



example1 :: IO ()
example1 =
  writeAnimationFrames (\n -> "p2p-relay3/frame-" ++ show n ++ ".png") 180 $
--  vizualise $
    scaleVizualisation 1.2 $
    viewportVizualisation 1920 1080 $
    timedVizualisation 0.1 $
    examplesVizualisation $
      traceRelayP2P
        (mkStdGen 4)
         P2PTopographyCharacteristics {
           p2pWorldDimensions  = (0.600, 0.300),
           p2pScreenDimensions = (1900, 1080),
           p2pNumNodes         = 100,
           p2pNodeLinksClose   = 5,
           p2pNodeLinksRandom  = 5
         }
        (\latency -> mkTcpConnProps latency (kilobytes 1000))
        (\rng ->
         RelayNodeConfig {
           blockProcessingDelay = const 0.1, -- 100ms
           blockGeneration      = PoissonGenerationPattern
                                    (kilobytes 96)
                                    rng
                                    (0.2 * 100) -- average seconds between blocks
                                    5.0
         })


examplesVizualisation :: RelaySimTrace
                      -> Vizualisation
examplesVizualisation =
    relayP2PSimVizualisation config
  where
    config :: RelayP2PSimVizConfig
    config =
      RelayP2PSimVizConfig {
        nodeMessageColor = testNodeMessageColor,
        ptclMessageColor = testPtclMessageColor
      }

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

