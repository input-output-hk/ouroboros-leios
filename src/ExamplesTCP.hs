{-# LANGUAGE NamedFieldPuns #-}
module ExamplesTCP where

import Data.Word

import Control.Monad.Class.MonadTime (Time, DiffTime)

import System.Random (mkStdGen, random)

import qualified Graphics.Rendering.Chart.Easy as Chart
import           Graphics.Rendering.Chart.Easy ((.=))

import ModelTCP
import SimTCPLinks
import Viz
import VizSim
import VizSimTCP
import PlotTCP
import VizChart


------------------------------------------------------------------------------
-- Example sim visualisations
--

example1 :: IO ()
example1 =
--    writeAnimationFrames (\n -> "output/tcp-chart-1/frame-" ++ show n ++ ".png") 55 $
    vizualise $
      slowmoVizualisation 0.1 $
      Viz (tcpSimVizModel (traceTcpLinks1 tcpprops trafficPattern))
          (aboveVizRender
             (labelVizRender title)
             (besideVizRender
               (aboveVizRender
                  labelTimeVizRender
                  (tcpSimVizRender examplesTcpSimVizConfig))
               (chartVizRender (500, 500) 25 chart)))
  where
    tcpprops       = mkTcpConnProps 0.3 (kilobytes 1000)
    trafficPattern = mkUniformTrafficPattern 20 (kilobytes 100) 0

    title = "Sending 20x 100kb messages over TCP"

    chart :: Time -> FrameNo -> TcpSimVizModel
          -> Chart.EC (Chart.Layout DiffTime Bytes) ()
    chart now _ (SimVizModel _ TcpSimVizState {vizTcpEvents}) = do
        Chart.layout_title .= "Cumulative kb transmitted"
        Chart.setColors [Chart.opaque Chart.blue, Chart.opaque Chart.red]
        Chart.plot (Chart.line "kb sent"
                      (tcpDataSeries BySegment DataSent (Just now) ds))
        Chart.plot (Chart.line "kb received"
                      (tcpDataSeries BySegment DataRecv (Just now) ds))
        return ()
      where
        ds = reverse vizTcpEvents

{-
example2 :: IO ()
example2 =
    vizualise $
      slowmoVizualisation 0.2 $
      aboveVizualisations
        (viewportVizualisation 1000 350 $
         examplesVizualisation $
           traceTcpLinks4 tcpprops1 tcpprops1 tcpprops1 trafficPattern)
        (viewportVizualisation 1000 400 $
         examplesVizualisation $
           traceTcpLinks4 tcpprops2 tcpprops2 tcpprops2 trafficPattern)
  where
    tcpprops1 = mkTcpConnProps 0.3 (kilobytes 1000)
    tcpprops2 = mkTcpConnProps 0.3 (kilobytes 10000)

    trafficPattern = mkUniformTrafficPattern 15 (kilobytes 100) 0

example3 :: IO ()
example3 =
    vizualise $
      slowmoVizualisation 0.2 $
      aboveVizualisations
        (viewportVizualisation 1000 350 $
         examplesVizualisation $
           traceTcpLinks4 tcpprops tcpprops tcpprops trafficPattern1)
        (viewportVizualisation 1000 680 $
         examplesVizualisation $
           traceTcpLinks4 tcpprops tcpprops tcpprops trafficPattern2)
  where
    tcpprops = mkTcpConnProps 0.3 (kilobytes 1000)

    trafficPattern1 = mkUniformTrafficPattern 15 (kilobytes 100) 1.2
    trafficPattern2 = mkUniformTrafficPattern 30 (kilobytes  50) 0.6
-}

examplesVizualisation :: TcpSimTrace -> Vizualisation
examplesVizualisation =
    tcpSimVizualisation examplesTcpSimVizConfig

examplesTcpSimVizConfig :: TcpSimVizConfig TestMessage
examplesTcpSimVizConfig =
    TcpSimVizConfig {
      messageColor
    }
  where
    messageColor :: TestMessage -> (Double, Double, Double)
    messageColor (TestMessage msgid _) =
        (fromIntegral r / 256, fromIntegral g / 256, fromIntegral b / 256)
      where
        r, g, b :: Word8
        ((r,g,b), _) = random (mkStdGen msgid)

