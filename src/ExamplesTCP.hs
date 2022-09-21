{-# LANGUAGE NamedFieldPuns #-}
module ExamplesTCP where

import Data.Word
import Data.Functor.Contravariant

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

example1 :: Vizualisation
example1 =
      slowmoVizualisation 0.1 $
      Viz model $
        LayoutAbove
          [ LayoutReqSize 100 25 $ layoutLabel title
          , LayoutBeside
              [ LayoutAbove
                  [ layoutLabelTime
                  , LayoutScaleFit $ Layout $
                      tcpSimVizRender examplesTcpSimVizConfig
                  ]
              , Layout $ chartVizRender 25 chart
              ]
          ]
  where
    model          = tcpSimVizModel trace
      where trace  = traceTcpLinks1 tcpprops trafficPattern
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

example2 :: Vizualisation
example2 =
    slowmoVizualisation 0.2 $
    Viz model $
      LayoutAbove
        [ layoutLabelTime
        , LayoutReqSize 1000 400 $
          Layout $ contramap fst $
            tcpSimVizRender examplesTcpSimVizConfig
        , LayoutReqSize 1000 400 $
          Layout $ contramap snd $
            tcpSimVizRender examplesTcpSimVizConfig
        ]
  where
    model     = pairVizModel
                  (tcpSimVizModel trace1)
                  (tcpSimVizModel trace2)
      where
        trace1 = traceTcpLinks4 tcpprops1 tcpprops1 tcpprops1 trafficPattern
        trace2 = traceTcpLinks4 tcpprops2 tcpprops2 tcpprops2 trafficPattern

    tcpprops1 = mkTcpConnProps 0.3 (kilobytes 1000)
    tcpprops2 = mkTcpConnProps 0.3 (kilobytes 10000)

    trafficPattern = mkUniformTrafficPattern 15 (kilobytes 100) 0

example3 :: Vizualisation
example3 =
    slowmoVizualisation 0.2 $
    Viz model $
      LayoutAbove
        [ layoutLabelTime
        , LayoutReqSize 1000 400 $
          Layout $ contramap fst $
            tcpSimVizRender examplesTcpSimVizConfig
        , LayoutReqSize 1000 680 $
          Layout $ contramap snd $
            tcpSimVizRender examplesTcpSimVizConfig
        ]
  where
    model     = pairVizModel
                  (tcpSimVizModel trace1)
                  (tcpSimVizModel trace2)
      where
        trace1 = traceTcpLinks4 tcpprops tcpprops tcpprops trafficPattern1
        trace2 = traceTcpLinks4 tcpprops tcpprops tcpprops trafficPattern2

    tcpprops = mkTcpConnProps 0.3 (kilobytes 1000)

    trafficPattern1 = mkUniformTrafficPattern 15 (kilobytes 100) 1.2
    trafficPattern2 = mkUniformTrafficPattern 30 (kilobytes  50) 0.6

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

