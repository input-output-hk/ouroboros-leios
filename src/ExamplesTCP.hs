{-# LANGUAGE NamedFieldPuns #-}
module ExamplesTCP where

import Data.Word

import SimTCPLinks
import Viz
import VizSimTCP
import VizChart

import System.Random (mkStdGen, random)

import qualified Graphics.Rendering.Chart.Easy as Chart
import           Graphics.Rendering.Chart.Easy ((.=))


------------------------------------------------------------------------------
-- Example sim visualisations
--

example1 :: IO ()
example1 =
--    writeAnimationFrames (\n -> "example1/frame-" ++ show n ++ ".png") 55 $
    vizualise $
      scaleVizualisation 2.0 $
      timedVizualisation 0.1 $
      besideVizualisations
        (examplesVizualisation $
          traceTcpLinks1 tcpprops trafficPattern)
        (chartVizualisation (500, 500) chart1)
  where
    tcpprops       = mkTcpConnProps 0.3 (kilobytes 1000)
    trafficPattern = mkUniformTrafficPattern 20 (kilobytes 100) 0

chart1 :: Chart.EC (Chart.Layout Double Double) ()
chart1 = do
    Chart.layout_title .= "Amplitude Modulation"
    Chart.setColors [Chart.opaque Chart.blue, Chart.opaque Chart.red]
    Chart.plot (Chart.line "am" [signal [0,(0.5)..400]])
    Chart.plot (Chart.points "am points" (signal [0,7..400]))
    return ()
  where
    signal :: [Double] -> [(Double,Double)]
    signal xs = [ (x,(sin (x*3.14159/45) + 1) / 2 * (sin (x*3.14159/5))) | x <- xs ]


example2 :: IO ()
example2 =
    vizualise $
      timedVizualisation 0.2 $
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
      timedVizualisation 0.2 $
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


examplesVizualisation :: TcpSimTrace -> Vizualisation
examplesVizualisation =
    tcpSimVizualisation config
  where
    config :: TcpSimVizConfig TestMessage
    config =
      TcpSimVizConfig {
        messageColor
      }

    messageColor :: TestMessage -> (Double, Double, Double)
    messageColor (TestMessage msgid _) =
        (fromIntegral r / 256, fromIntegral g / 256, fromIntegral b / 256)
      where
        r, g, b :: Word8
        ((r,g,b), _) = random (mkStdGen msgid)

