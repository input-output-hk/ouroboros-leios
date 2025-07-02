{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE ParallelListComp #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module Test.ShortToFull where

import Data.Default (def)
import Data.List (sort)
import LeiosProtocol.Common (InputBlockId (..), NodeId (..), SlotNo)
import LeiosProtocol.Config (Config)
import qualified LeiosProtocol.Short as Short
import Test.QuickCheck as Q
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.QuickCheck (testProperty)

tests :: TestTree
tests =
  testGroup
    "ShortToFull"
    [ testProperty "test_leiosLateIbInclusion" test_leiosLateIbInclusion
    ]

data Test_leiosLateIbInclusion = Test_leiosLateIbInclusion
  { ibTable :: [(Int, Short.PipelineNo, Short.IbDeliveryStage)] -- the Int is @zip [0..]@, /before shrinking/
  , ebLo :: SlotNo
  -- ^ this first slot in which an EB could actually exist
  , ebSlot :: SlotNo
  }
  deriving (Show)

instance Q.Arbitrary Test_leiosLateIbInclusion where
  arbitrary = do
    let cfg = Short.convertConfig def
    let (ebLo, ebHi) = case cfg of
          Short.LeiosConfig{pipeline = _ :: Short.SingPipeline p} ->
            Short.stageRangeOf @p cfg (toEnum 0) Short.Endorse
    ebSlot <- toEnum <$> Q.choose (fromEnum ebLo, fromEnum ebHi + 9 * cfg.sliceLength)
    ibTable <- do
      n <- Q.choose (0, 1000)
      gens <- Q.vectorOf n $ fmap toEnum $ Q.choose (0, 20)
      delays <- Q.vectorOf n $ Q.elements [minBound .. maxBound]
      pure $ [(i, gen, delay) | i <- [0 ..] | gen <- sort gens | delay <- delays]
    pure Test_leiosLateIbInclusion{..}

  shrink testSetup =
    [ testSetup{ibTable = ibTable'}
    | ibTable' <- shrinkList (const []) testSetup.ibTable
    ]

test_leiosLateIbInclusion :: Test_leiosLateIbInclusion -> Property
test_leiosLateIbInclusion testSetup =
  Q.counterexample (show (cfg.sliceLength, iterations))
    $ Q.counterexample ("ebPipeline " <> show (fromEnum ebSlot `div` cfg.sliceLength))
    $ Q.counterexample ("on " <> show (map (.num) on))
    $ Q.counterexample
      (unlines $ ("off" :) $ map (show . map (.num) . off) $ iterations)
    $ on Q.=== concatMap off iterations
 where
  Test_leiosLateIbInclusion{..} = testSetup
  cfg = Short.convertConfig def
  ibSnapshot =
    Short.InputBlocksSnapshot
      { validInputBlocks = \q ->
          [ InputBlockId{node = NodeId 0, num = i}
          | (i, gen, recv) <- ibTable
          , gen `Short.inRange` q.generatedBetween
          , recv <= q.receivedBy
          ]
      }
  on =
    Short.inputBlocksToEndorse
      cfg{Short.lateIbInclusion = True}
      ebSlot
      ibSnapshot
  off sl =
    Short.inputBlocksToEndorse
      cfg{Short.lateIbInclusion = False}
      sl
      ibSnapshot
  iterations =
    let capL = fromIntegral cfg.sliceLength
     in -- discard underflow and negative iterations
        dropWhile (\sl -> sl > ebSlot || sl < ebLo) [ebSlot - 2 * capL, ebSlot - capL, ebSlot]
