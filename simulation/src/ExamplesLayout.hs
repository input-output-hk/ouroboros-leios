{-# LANGUAGE NamedFieldPuns #-}

module ExamplesLayout where

import Viz

import qualified Graphics.Rendering.Cairo as Cairo
import Numeric

------------------------------------------------------------------------------
-- Example layouts for vizualisation
--

-- Use: vizualise defaultGtkVizConfig exampleN

example1 :: Vizualisation
example1 =
  Viz nullVizModel $
    LayoutAbove
      [ baseLayout (100, 100) "Block 1" (1, 0, 0)
      , baseLayout (100, 100) "Block 2" (0, 1, 0)
      , baseLayout (100, 100) "Block 3" (0, 0, 1)
      ]

example2 :: Vizualisation
example2 =
  Viz nullVizModel $
    LayoutBeside
      [ LayoutFixed $
          LayoutAbove
            [ baseLayout (200, 100) "Block 1" (1, 0, 0)
            , baseLayout (100, 200) "Block 2" (0, 1, 0)
            , baseLayout (200, 200) "Block 3" (0, 0, 1)
            ]
      , LayoutAbove
          [ LayoutFixed $
              baseLayout (200, 100) "Block 4" (1, 0, 1)
          , baseLayout (100, 200) "Block 5" (1, 1, 0)
          , baseLayout (200, 200) "Block 6" (0, 1, 1)
          ]
      ]

example3 :: Vizualisation
example3 =
  Viz nullVizModel $
    LayoutAbove
      [ LayoutFixed $ baseLayout (100, 100) "Block 1" (1, 0, 0)
      , LayoutAspect $
          LayoutReqSize 200 200 $
            baseLayout (100, 100) "Block 2" (0, 1, 0)
      ]

example4 :: Vizualisation
example4 =
  Viz nullVizModel $
    LayoutAbove
      [ LayoutScaleBy 2.0 $
          baseLayout (100, 100) "Block 1" (1, 0, 0)
      , LayoutScaleFit $
          baseLayout (100, 100) "Block 2" (0, 1, 0)
      , LayoutScaleFit $
          LayoutAspect $
            baseLayout (100, 100) "Block 3" (0, 0, 1)
      ]

example5 :: Vizualisation
example5 =
  Viz nullVizModel $
    LayoutAbove
      [ layoutLabel 18 "Example title"
      , LayoutBeside
          [ LayoutAbove
              [ layoutLabelTime
              , LayoutScaleFit $
                  baseLayout (100, 100) "Block 1" (1, 0, 0)
              ]
          , baseLayout (100, 100) "Block 2" (0, 1, 0)
          ]
      ]

example6 :: Vizualisation
example6 =
  slowmoVizualisation 0.1 $
    Viz nullVizModel $
      LayoutAbove
        [ layoutLabelTime
        , Layout $
            VizRender
              { renderReqSize = (200, 200)
              , renderChanged = \_t _fn _m -> True
              , renderModel = \t fn _m (w, h) -> do
                  Cairo.rectangle 10 10 (w - 20) (h - 20)
                  Cairo.setSourceRGBA 0.5 0.5 0.5 (fromIntegral (fn `mod` 25) / 50)
                  Cairo.fill
                  Cairo.setSourceRGB 0 0 0
                  Cairo.moveTo (w / 2) (h / 2)
                  Cairo.showText (show t)
                  Cairo.moveTo (w / 2) (h / 2 + 20)
                  Cairo.showText (show fn)
              }
        ]

baseLayout :: (Int, Int) -> String -> (Double, Double, Double) -> Layout (VizRender a)
baseLayout renderReqSize label colour =
  Layout $
    VizRender
      { renderReqSize
      , renderChanged = \_t _fn _m -> False
      , renderModel = \_t _fn _m -> renderBlock label colour
      }

renderBlock ::
  String ->
  (Double, Double, Double) ->
  (Double, Double) ->
  Cairo.Render ()
renderBlock label (r, g, b) (w, h) = do
  Cairo.rectangle 0 0 w h
  Cairo.setSourceRGB r g b
  Cairo.fillPreserve

  Cairo.setSourceRGB 0.7 0.7 0.7
  Cairo.setLineWidth 2
  Cairo.stroke

  Cairo.moveTo 0 0
  Cairo.lineTo w h
  Cairo.stroke
  Cairo.moveTo w 0
  Cairo.lineTo 0 h
  Cairo.stroke

  Cairo.moveTo (w / 2) (h / 2)
  Cairo.setSourceRGB 0 0 0
  Cairo.showText label

  Cairo.moveTo (w / 2) (h / 2 + 20)
  Cairo.showText (showFFloat (Just 2) w "")
  Cairo.moveTo (w / 2) (h / 2 + 40)
  Cairo.showText (showFFloat (Just 2) h "")
