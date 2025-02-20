{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Leios.Conformance.Test where

import Data.List (sort)
import Data.Maybe (isJust)
import Data.Text (Text, intercalate, pack)
import Test.QuickCheck (
  Arbitrary (..),
  Gen,
  chooseInteger,
  frequency,
  suchThat,
 )
import Test.QuickCheck.DynamicLogic (DynLogicModel)
import Test.QuickCheck.StateModel (
  Any (Some),
  HasVariables (..),
  StateModel (
    Action,
    arbitraryAction,
    initialState,
    nextState,
    precondition,
    shrinkAction
  ),
 )
import Text.PrettyPrint ((<+>))
import Text.PrettyPrint.HughesPJClass (
  Pretty (pPrint),
 )

import Leios.Conformance.Model (
  EndorserBlock (..),
  EnvAction (..),
  IBBody (..),
  IBHeader (..),
  InputBlock (..),
  LeiosState (..),
  NodeModel (..),
  Vote,
  initialModelState,
  transition,
 )

data NetworkModel = NetworkModel
  { nodeModel :: NodeModel
  , initialized :: Bool
  }
  deriving (Show)

instance HasVariables NetworkModel where
  getAllVariables _ = mempty

instance DynLogicModel NetworkModel

instance Show (Action NetworkModel a) where
  show (Step a) = show a
deriving instance Eq (Action NetworkModel a)

instance HasVariables (Action NetworkModel a) where
  getAllVariables _ = mempty

instance Pretty EnvAction where
  pPrint Tick = "Tick"
  pPrint (NewIB ib) = "NewIB" <+> pPrint ib
  pPrint (NewEB eb) = "NewEB" <+> pPrint eb
  pPrint (NewVote v) = "NewVote" <+> pPrint v

genPositiveInteger :: Gen Integer
genPositiveInteger = abs <$> arbitrary

genSlot :: Gen Integer
genSlot = genPositiveInteger

genProducer :: Gen Integer
genProducer = pure 0 -- FIXME: different parties

genSortedList :: Gen [Integer]
genSortedList = sort <$> arbitrary

instance Arbitrary InputBlock where
  arbitrary = do
    b <- IBBody <$> genSortedList
    let t = hash (txs b)
    h <- IBHeader <$> genSlot <*> genProducer <*> pure t
    pure $ InputBlock h b
   where
    hash :: [Integer] -> Text
    hash = intercalate "#" . map (pack . show)

instance Arbitrary EndorserBlock where
  arbitrary =
    let ibs = arbitrary :: Gen [InputBlock]
        ibRefs = map (bodyHash . header) <$> ibs
     in EndorserBlock <$> genSlot <*> genProducer <*> ibRefs

instance StateModel NetworkModel where
  data Action NetworkModel a where
    Step :: EnvAction -> Action NetworkModel ([InputBlock], [EndorserBlock], [[Vote]])

  initialState =
    NetworkModel
      { nodeModel = initialModelState
      , initialized = True
      }

  arbitraryAction _ NetworkModel{nodeModel = LeiosState{..}} = do
    fmap (Some . Step) . frequency $
      [(1, pure Tick)]
        ++ fmap (10,) [NewIB <$> arbitrary]
        ++ fmap (1,) [NewEB <$> arbitrary]
        ++ fmap (1,) [NewVote <$> arbitrary]

  shrinkAction _ _ (Step Tick) = []
  shrinkAction _ _ Step{} = [Some (Step Tick)]

  precondition NetworkModel{nodeModel = s} (Step a) = isJust $ transition s a

  nextState net@NetworkModel{nodeModel = s} (Step a) _ = net{nodeModel = maybe s snd $ transition s a}
