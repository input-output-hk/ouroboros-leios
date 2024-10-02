module ExamplesRelay where

import Data.Word
import System.Random (mkStdGen, uniform)

import RelayProtocol
import SimTCPLinks (mkTcpConnProps, kilobytes)
import Viz
import VizSimRelay
import SimRelay


example1 :: Vizualisation
example1 =
    slowmoVizualisation 0.1 $
    Viz model $
      LayoutReqSize 500 650 $
      Layout $ relaySimVizRender examplesRelaySimVizConfig
  where
    model = relaySimVizModel trace
      where
        trace = traceRelayLink1
                  (mkTcpConnProps 0.3 (kilobytes 1000))
                  (UniformGenerationPattern (kilobytes 100) 0.2 5.0)


example2 :: Vizualisation
example2 =
    slowmoVizualisation 0.1 $
    Viz model $
      LayoutReqSize 1000 650 $
      Layout $ relaySimVizRender examplesRelaySimVizConfig
  where
    model = relaySimVizModel trace
      where
        trace = traceRelayLink4
                  (mkTcpConnProps 0.3 (kilobytes 1000))
                  (UniformGenerationPattern (kilobytes 100) 0.2 5.0)


example3 :: Vizualisation
example3 =
    slowmoVizualisation 0.1 $
    Viz model $
      LayoutReqSize 1000 650 $
      Layout $ relaySimVizRender examplesRelaySimVizConfig
  where
    model = relaySimVizModel trace
      where
        trace = traceRelayLink4Asymmetric
                  (mkTcpConnProps 0.2 (kilobytes 1000))
                  (mkTcpConnProps 0.3 (kilobytes 1000))
                  (UniformGenerationPattern (kilobytes 100) 0.2 5.0)


examplesRelaySimVizConfig :: RelaySimVizConfig
examplesRelaySimVizConfig =
    RelaySimVizConfig {
      nodeMessageColor = testNodeMessageColor,
      ptclMessageColor = testPtclMessageColor,
      nodeMessageText  = testNodeMessageText,
      ptclMessageText  = testPtclMessageText
    }
  where
    testPtclMessageColor :: BlockRelayMessage TestBlock TestBlockId BlockTTL
                         -> (Double, Double, Double)
    testPtclMessageColor (MsgRespBlock blk) = testNodeMessageColor blk
    testPtclMessageColor _                = (1, 0, 0)

    testNodeMessageColor :: TestBlock -> (Double, Double, Double)
    testNodeMessageColor (TestBlock (TestBlockId blkid) _ _) =
        (fromIntegral r / 256, fromIntegral g / 256, fromIntegral b / 256)
      where
        r, g, b :: Word8
        ((r,g,b), _) = uniform (mkStdGen blkid)

    testNodeMessageText :: TestBlock -> Maybe String
    testNodeMessageText (TestBlock (TestBlockId blkid) _ _) = Just (show blkid)

    testPtclMessageText :: BlockRelayMessage TestBlock TestBlockId BlockTTL
                        -> Maybe String
    testPtclMessageText  MsgReqBlockIdsBlocking    = Just "ReqBlockIdsBlocking"
    testPtclMessageText  MsgReqBlockIdsNonBlocking = Just "ReqBlockIdsNonBlocking"
    testPtclMessageText  MsgRespBlockIds{}         = Just "RespBlockIds"
    testPtclMessageText (MsgReqBlock blkid)        = Just ("ReqBlock " ++ show n)
                                                 where TestBlockId n = blkid
    testPtclMessageText (MsgRespBlock blk)         = ("RespBlock " ++) <$> testNodeMessageText blk
    testPtclMessageText  MsgRespNoBlock{}          = Just "RespNoBlock"

