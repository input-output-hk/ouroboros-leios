{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE RecordWildCards #-}

module Test.ShortToFull where

import Data.Default (def)
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
  { ibTable :: [(Int, SlotNo, SlotNo)] -- the Int is @zip [0..]@, /before shrinking/
  , current :: SlotNo
  }
  deriving (Show)

instance Q.Arbitrary Test_leiosLateIbInclusion where
  arbitrary = do
    let cfg = Short.convertConfig def
    let arbSlot = Q.choose (0, 10 * cfg.sliceLength)
    let toSlot :: Int -> SlotNo
        toSlot = toEnum
    current <- toSlot <$> arbSlot
    ibTable <- do
      n <- Q.choose (0, 1000)
      flip mapM [0 .. n - 1] $ \i -> do
        gen <- Q.choose (0, fromEnum current)
        delay <- Q.choose (0, 3 * cfg.sliceLength)
        pure (i, toSlot gen, toSlot (gen + delay))
    pure Test_leiosLateIbInclusion{..}

  shrink testSetup =
    [ testSetup{ibTable = ibTable'}
    | ibTable' <- shrinkList (const []) testSetup.ibTable
    ]

test_leiosLateIbInclusion :: Test_leiosLateIbInclusion -> Property
test_leiosLateIbInclusion testSetup =
  Q.counterexample (show (cfg.sliceLength, iterations))
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
      current
      ibSnapshot
  off sl =
    Short.inputBlocksToEndorse
      cfg{Short.lateIbInclusion = False}
      sl
      ibSnapshot
  iterations =
    let capL = fromIntegral cfg.sliceLength
     in -- detect underflow
        dropWhile (> current) [current - 2 * capL, current - capL, current]
