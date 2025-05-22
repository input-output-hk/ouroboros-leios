{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}

module Spec.Generated where

import Control.Monad (liftM2, mzero, replicateM)
import Data.List (inits)
import Data.Text (Text)
import LeiosConfig (leiosStageLengthSlots)
import LeiosEvents
import LeiosTopology (nodeInfo, nodes, stake, unNodeName)
import Lib (verifyTrace)
import Spec.Transition
import Test.Hspec
import Test.Hspec.QuickCheck
import Test.QuickCheck hiding (scale)

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

data Check
  = MustBeOkay
  | MustNotBeOkay
  | MustBe Text
  deriving (Show)

check ::
  Maybe Integer ->
  Check ->
  [TraceEvent] ->
  Property
check expectedActions expectedMessage events =
  let
    result = verify events
    checkMessage =
      case expectedMessage of
        MustBeOkay -> (=== "ok")
        MustNotBeOkay -> (=/= "ok")
        MustBe expectedMessage' -> (=== expectedMessage')
   in
    case expectedActions of
      Nothing -> checkMessage $ snd result
      Just expectedActions' -> fst result === expectedActions' .&&. checkMessage (snd result)

newtype SkipProduction = SkipProduction {unSkipProduction :: [Transition]}
  deriving (Show)

instance Arbitrary SkipProduction where
  arbitrary =
    do
      let gOdd = (NextSlot :) <$> shuffle [SkipIB, SkipVT]
          gEven = (NextSlot :) <$> shuffle [SkipIB, SkipEB, SkipVT]
          g = liftM2 (<>) gOdd gEven
      n <- choose (1, 25)
      SkipProduction . concat <$> replicateM n g
  shrink = fmap SkipProduction . init . inits . unSkipProduction

newtype SporadicProduction = SporadicProduction {unSporadicProduction :: [Transition]}
  deriving (Show)

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
          g = liftM2 (<>) gOdd gEven
      n <- choose (1, 25)
      SporadicProduction . concat <$> replicateM n g
  shrink = fmap SporadicProduction . init . inits . unSporadicProduction

newtype NoisyProduction = NoisyProduction {unNoisyProduction :: [Transition]}
  deriving (Show)

instance Arbitrary NoisyProduction where
  arbitrary =
    do
      let gNoise = sublistOf [GenerateRB, ReceiveRB, ReceiveIB, ReceiveEB, ReceiveVT]
          gIB = elements [GenerateIB, SkipIB]
          gEB = elements [GenerateEB, SkipEB]
          gVT = elements [GenerateVT, SkipVT]
          gOdd =
            do
              noise <- gNoise
              ib <- gIB
              vt <- gVT
              (NextSlot :) <$> shuffle ([ib, vt] <> noise)
          gEven =
            do
              noise <- gNoise
              ib <- gIB
              eb <- gEB
              vt <- gVT
              (NextSlot :) <$> shuffle ([ib, eb, vt] <> noise)
          g = liftM2 (<>) gOdd gEven
      n <- choose (1, 25)
      NoisyProduction . concat <$> replicateM n g
  shrink = fmap NoisyProduction . init . inits . unNoisyProduction

newtype SporadicMisses = SporadicMisses {unSporadicMisses :: [Transition]}
  deriving (Show)

instance Arbitrary SporadicMisses where
  arbitrary =
    do
      valid <- unSporadicProduction <$> arbitrary
      i <- choose (1, length valid - 1)
      pure . SporadicMisses $ take i valid <> drop (i + 1) valid <> pure NextSlot

generated :: Spec
generated =
  do
    let single = (modifyMaxSuccess (const 1) .) . prop
    describe "Positive cases" $ do
      single "Genesis slot" $
        check mzero MustBeOkay
          <$> transitions [NextSlot]
      single "Generate RB" $
        check mzero MustBeOkay
          <$> transitions [NextSlot, GenerateRB]
      single "Generate IB" $
        check mzero MustBeOkay
          <$> transitions [NextSlot, GenerateIB]
      single "Generate no IB" $
        check mzero MustBeOkay
          <$> transitions [NextSlot, SkipIB]
      single "Generate EB" $
        check mzero MustBeOkay
          <$> transitions [NextSlot, SkipIB, SkipVT, NextSlot, GenerateEB]
      single "Generate no EB" $
        check mzero MustBeOkay
          <$> transitions [NextSlot, SkipIB, SkipVT, NextSlot, SkipEB]
      single "Generate VT" $
        check mzero MustBeOkay
          <$> transitions [NextSlot, GenerateVT]
      single "Generate no VT" $
        check mzero MustBeOkay
          <$> transitions [NextSlot, SkipVT]
      prop "Skip block production" $ \(SkipProduction actions) ->
        check mzero MustBeOkay <$> transitions actions
      prop "Sporadic block production" $ \(SporadicProduction actions) ->
        check mzero MustBeOkay <$> transitions actions
      prop "Noisy block production" $ \(NoisyProduction actions) ->
        check mzero MustBeOkay <$> transitions actions
    describe "Negative cases" $ do
      single "No actions" $
        check mzero (MustBe "Invalid Action: Slot Slot-Action 1")
          <$> transitions [NextSlot, NextSlot]
      single "Start after genesis" $
        check mzero (MustBe "Invalid Action: Slot Base\8322b-Action 1")
          <$> transitions [SkipSlot, NextSlot]
      single "Generate equivocated IBs" $
        check mzero (MustBe "Invalid Action: Slot IB-Role-Action 1")
          <$> transitions [NextSlot, GenerateIB, GenerateIB]
      single "Generate equivocated EBs" $
        check mzero (MustBe "Invalid Action: Slot EB-Role-Action 2")
          <$> transitions [NextSlot, SkipIB, SkipVT, NextSlot, GenerateEB, GenerateEB]
      single "Generate equivocated VTs" $
        check mzero (MustBe "Invalid Action: Slot VT-Role-Action 1")
          <$> transitions [NextSlot, GenerateVT, GenerateVT]
      prop "Sporadic gaps in production" $ \(SporadicMisses actions) ->
        check mzero MustNotBeOkay <$> transitions actions
