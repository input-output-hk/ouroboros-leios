{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}

-- | Arbitrary and generated tests.
module Spec.Generated where

import Control.Monad (join, liftM2, mzero, replicateM)
import Data.List (inits)
import Data.Text (Text)
import LeiosConfig
import LeiosEvents
import LeiosTopology (nodeInfo, nodes, stake, unNodeName)
import ShortLeiosLib (verifyTrace)
import Spec.Transition
import Test.Hspec
import Test.Hspec.QuickCheck
import Test.QuickCheck hiding (scale)

import qualified Data.Map.Strict as M
import qualified Spec.Scenario as Scenario (config, idSut, topology)

-- | Run the verify on a list of events.
verify :: [TraceEvent] -> (Integer, (Text, Text))
verify =
  let
    nrNodes = toInteger . M.size $ nodes Scenario.topology
    nodeNames = unNodeName <$> (M.keys $ nodes Scenario.topology)
    stakes = toInteger . stake . nodeInfo <$> (M.elems $ nodes Scenario.topology)
    stakeDistribution = zip nodeNames stakes
    stageLength' = toInteger $ leiosStageLengthSlots Scenario.config
    ledgerQuality = ceiling (praosChainQuality Scenario.config) -- TODO: int in schema?
    lateIBInclusion = leiosLateIbInclusion Scenario.config
   in
    verifyTrace nrNodes Scenario.idSut stakeDistribution stageLength' ledgerQuality lateIBInclusion

-- | Expectation for checking a trace.
data Check
  = MustBeOkay
  | MustNotBeOkay
  | MustBe Text
  deriving (Show)

-- | Check that a trace has the expected number of actions and result.
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
      Nothing -> checkMessage $ fst (snd result)
      Just expectedActions' -> fst result === expectedActions' .&&. checkMessage (fst (snd result))

-- | Generate the initial IB and events leading up to it.
initStageIB :: Gen [Transition]
initStageIB =
  let
    stageLength' = fromIntegral $ leiosStageLengthSlots Scenario.config
    gIB = elements [GenerateIB, SkipIB]
   in
    join <$> replicateM stageLength' ((: [NextSlot]) <$> gIB)

-- | Generate the initial EB and events leading up to it.
initStageEB :: Gen [Transition]
initStageEB =
  let
    stageLength' = fromIntegral $ leiosStageLengthSlots Scenario.config
    gIB = elements [GenerateIB, SkipIB]
    gEB = elements [GenerateEB, SkipEB]
   in
    do
      ib <- gIB
      eb <- gEB
      l <- shuffle [ib, eb]
      a <- join <$> replicateM (stageLength' - 1) ((: [NextSlot]) <$> gIB)
      pure $ l ++ [NextSlot] ++ a

-- | Generate the initial vote and events leading up to it.
initStageVT :: Gen [Transition]
initStageVT =
  let
    stageLength' = fromIntegral $ leiosStageLengthSlots Scenario.config
    gIB = elements [GenerateIB, SkipIB]
    gEB = elements [GenerateEB, SkipEB]
    gVT = elements [GenerateVT, SkipVT]
   in
    do
      ib <- gIB
      eb <- gEB
      l <- shuffle [ib, eb]
      a <-
        join
          <$> replicateM
            (stageLength' - 1)
            ( do
                ib' <- gIB
                vt' <- gVT
                l' <- shuffle [ib', vt']
                pure $ l' ++ [NextSlot]
            )
      pure $ l ++ [NextSlot] ++ a

-- | Generate the initial events.
initPipelines :: Gen [Transition]
initPipelines = do
  s1 <- initStageIB
  s2 <- initStageIB
  s3 <- initStageIB
  s4 <- initStageEB
  s5 <- initStageVT
  pure $ s1 ++ s2 ++ s3 ++ s4 ++ s5

-- | Wrapper for skipping production of RBs, IBs, EBs, or votes.
newtype SkipProduction = SkipProduction {unSkipProduction :: [Transition]}
  deriving (Show)

instance Arbitrary SkipProduction where
  arbitrary =
    do
      let gOdd = (++ [NextSlot]) <$> shuffle [SkipIB]
          gEven = (++ [NextSlot]) <$> shuffle [SkipIB, SkipEB, SkipVT]
          g = liftM2 (<>) gEven gOdd
      n <- choose (1, 25)
      i <- initPipelines
      r <- concat <$> replicateM n g
      pure $ SkipProduction (i ++ r)
  shrink = fmap SkipProduction . init . inits . unSkipProduction

-- | Wrapper for sporadic production of RBs, IBs, EBs, or votes.
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
              (++ [NextSlot]) <$> shuffle [ib]
          gEven =
            do
              ib <- gIB
              eb <- gEB
              vt <- gVT
              (++ [NextSlot]) <$> shuffle [ib, eb, vt]
          g = liftM2 (<>) gEven gOdd
      n <- choose (1, 25)
      i <- initPipelines
      r <- concat <$> replicateM n g
      pure $ SporadicProduction (i ++ r)
  shrink = fmap SporadicProduction . init . inits . unSporadicProduction

-- | Wrapper for noisy production (i.e., shuffled) of RBs, IBs, EB, and votes.
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
              (++ [NextSlot]) <$> shuffle ([ib] <> noise)
          gEven =
            do
              noise <- gNoise
              ib <- gIB
              eb <- gEB
              vt <- gVT
              (++ [NextSlot]) <$> shuffle ([ib, eb, vt] <> noise)
          g = liftM2 (<>) gEven gOdd
      n <- choose (1, 25)
      i <- initPipelines
      r <- concat <$> replicateM n g
      pure $ NoisyProduction (i ++ r)
  shrink = fmap NoisyProduction . init . inits . unNoisyProduction

-- | Wrapper for sporadically missing RBs, IBs, EB, and votes.
newtype SporadicMisses = SporadicMisses {unSporadicMisses :: [Transition]}
  deriving (Show)

instance Arbitrary SporadicMisses where
  arbitrary =
    do
      valid <- unSporadicProduction <$> arbitrary
      i <- choose (1, length valid - 1)
      pure . SporadicMisses $ take i valid <> drop (i + 1) valid <> pure NextSlot

-- | Generate tests.
generated :: Spec
generated =
  do
    let single = (modifyMaxSuccess (const 1) .) . prop
    describe "Positive cases" $ do
      single "Genesis slot" $
        check mzero MustBeOkay
          <$> transitions [SkipIB, NextSlot]
      single "Generate RB" $
        check mzero MustBeOkay
          <$> transitions [SkipIB, NextSlot, GenerateRB]
      single "Generate IB" $
        check mzero MustBeOkay
          <$> transitions [SkipIB, NextSlot, GenerateIB]
      single "Generate no IB" $
        check mzero MustBeOkay
          <$> transitions [SkipIB, NextSlot, SkipIB]
      single "Generate EB" $
        check mzero MustBeOkay
          <$> transitions [SkipIB, NextSlot, SkipIB, SkipVT, NextSlot, GenerateEB]
      single "Generate no EB" $
        check mzero MustBeOkay
          <$> transitions [SkipIB, NextSlot, SkipIB, SkipVT, NextSlot, SkipEB]
      single "Generate VT" $
        check mzero MustBeOkay
          <$> transitions [SkipIB, NextSlot, GenerateVT]
      single "Generate no VT" $
        check mzero MustBeOkay
          <$> transitions [SkipIB, NextSlot, SkipVT]
      prop "Skip block production" $ \(SkipProduction actions) ->
        check mzero MustBeOkay <$> transitions actions
      prop "Sporadic block production" $ \(SporadicProduction actions) ->
        check mzero MustBeOkay <$> transitions actions
      prop "Noisy block production" $ \(NoisyProduction actions) ->
        check mzero MustBeOkay <$> transitions actions
    describe "Negative cases" $ do
      single "No actions" $
        check mzero (MustBe "Transition Error")
          <$> transitions [SkipIB, NextSlot, NextSlot]
      single "Start after genesis" $
        check mzero (MustBe "Invalid Slot")
          <$> transitions [SkipSlot, NextSlot]
      {- TODO: equivocation not prohibited in the formal spec
      single "Generate equivocated IBs" $
        check mzero (MustBe "Invalid Action: Slot IB-Role-Action 1")
          <$> transitions [GenerateIB, GenerateIB, NextSlot]
      -}
      single "Failure to generate IB" $
        check mzero (MustBe "Transition Error")
          <$> transitions [SkipIB, NextSlot, NextSlot]
      {- TODO: equivocation not prohibited in the formal spec
      single "Generate equivocated EBs" $
        check mzero (MustBe "Invalid Action: Slot EB-Role-Action 2")
          <$> transitions [SkipIB, NextSlot, SkipIB, SkipVT, NextSlot, GenerateEB, GenerateEB]
      -}
      single "Failure to generate EB" $
        check mzero (MustBe "Transition Error")
          <$> transitions [SkipIB, NextSlot, SkipIB, NextSlot, SkipIB, NextSlot, SkipIB, NextSlot, SkipIB, NextSlot, SkipIB, NextSlot, SkipIB, NextSlot]
      {- TODO: equivocation not prohibited in the formal spec
      single "Generate equivocated VTs" $
        check mzero (MustBe "Invalid Action: Slot VT-Role-Action 1")
          <$> transitions [SkipIB, NextSlot, SkipIB, NextSlot, SkipIB, NextSlot, SkipIB, NextSlot, SkipIB, NextSlot, SkipIB, NextSlot, SkipIB, SkipEB, NextSlot, SkipIB, NextSlot, SkipIB, SkipEB, GenerateVT, NextSlot, SkipIB, GenerateVT, NextSlot]
      -}
      single "Failure to generate VT" $
        check mzero (MustBe "Transition Error")
          <$> transitions [SkipIB, NextSlot, SkipIB, NextSlot, SkipIB, NextSlot, SkipIB, NextSlot, SkipIB, NextSlot, SkipIB, NextSlot, SkipIB, SkipEB, NextSlot, SkipIB, NextSlot, SkipIB, SkipEB, NextSlot, SkipIB, NextSlot]

{- TODO: equivocation not prohibited in the formal spec
prop "Sporadic gaps in production" $ \(SporadicMisses actions) ->
  check mzero MustNotBeOkay <$> transitions actions
-}
