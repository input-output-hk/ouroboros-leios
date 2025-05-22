{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}

module Spec.Generated where

import Control.Monad (liftM2, mzero, replicateM)
import Data.List (inits)
import Data.Maybe (fromMaybe)
import Data.Text (Text)
import LeiosConfig (leiosStageLengthSlots)
import LeiosEvents
import LeiosTopology (nodeInfo, nodes, stake, unNodeName)
import Lib (verifyTrace)
import Spec.Transition
import Test.Hspec
import Test.QuickCheck hiding (scale)
import Test.Hspec.QuickCheck

import qualified Data.Map.Strict as M
import qualified Spec.Scenario as Scenario (config, idSut, topology)

verify :: [TraceEvent] -> (Integer, Text)
verify =
  let
    nrNodes = toInteger . M.size $ nodes Scenario.topology
    nodeNames = unNodeName <$> (M.keys $ nodes Scenario.topology)
    stakes = toInteger . stake . nodeInfo <$> (M.elems $ nodes Scenario.topology)
    stakeDistribution = zip nodeNames stakes
    stageLength' = toInteger $ leiosStageLengthSlots Scenario.config
  in
    verifyTrace nrNodes Scenario.idSut stakeDistribution stageLength'

check
  :: Maybe Integer
  -> Maybe Text
  -> [TraceEvent]
  -> Property
check expectedActions expectedMessage events =
  let
    result = verify events
    expectedMessage' = fromMaybe "ok" expectedMessage
  in
    case expectedActions of
      Nothing -> snd result === expectedMessage'
      Just expectedActions' -> result === (expectedActions', expectedMessage')

newtype SkipProduction = SkipProduction {unSkipProduction :: [Transition]}
  deriving Show

instance Arbitrary SkipProduction where
  arbitrary =
    do
      let gOdd = (NextSlot :) <$> shuffle [SkipIB, SkipVT]
          gEven = (NextSlot :) <$> shuffle [SkipIB, SkipEB, SkipVT]
          g = liftM2 (<>) gOdd gEven
      n <- choose (0, 25)
      SkipProduction . concat <$> replicateM n g
  shrink = fmap SkipProduction . init . inits . unSkipProduction

newtype SporadicProduction = SporadicProduction {unSporadicProduction :: [Transition]}
  deriving Show

instance Arbitrary SporadicProduction where
  arbitrary = 
    do
      let gIB = elements [GenerateIB, SkipIB]
          gEB = elements [GenerateEB, SkipEB]
          gVT = elements [GenerateVT, SkipVT]
          gOdd =
            do
              ib <- gIB
              vt <- gVT
              (NextSlot :) <$> shuffle [ib, vt]
          gEven =
            do
              ib <- gIB
              eb <- gEB
              vt <- gVT
              (NextSlot :) <$> shuffle [ib, eb, vt]
          g= liftM2 (<>) gOdd gEven
      n <- choose (0, 25)
      SporadicProduction . concat <$> replicateM n g

generated :: Spec
generated =
  do
    let single = (modifyMaxSuccess (const 1) .) . prop

    describe "Positive cases" $ do
      single "Genesis slot" $
        check mzero mzero
          <$> transitions [NextSlot]
      prop "Skip block production" $ \(SkipProduction actions) ->
        check mzero mzero <$> transitions actions
      prop "Sporadic block production" $ \(SporadicProduction actions) ->
        check mzero mzero <$> transitions actions
      single "Generate RB" $
        check mzero mzero
          <$> transitions [NextSlot, GenerateRB]
      single "Generate IB" $
        check mzero mzero
          <$> transitions [NextSlot, GenerateIB]
      single "Generate no IB" $
        check mzero mzero
          <$> transitions [NextSlot, SkipIB]

    describe "Negative cases" $ do
      single "No actions" $
        check mzero (pure "Invalid Action: Slot Slot-Action 1")
          <$> transitions [NextSlot, NextSlot]
      single "Start after genesis" $
        check mzero (pure "Invalid Action: Slot Base\8322b-Action 1")
          <$> transitions [SkipSlot, NextSlot]
      single "Generate equivocated IBs" $
        check mzero (pure "Invalid Action: Slot IB-Role-Action 1")
          <$> transitions [NextSlot, GenerateIB, GenerateIB]
