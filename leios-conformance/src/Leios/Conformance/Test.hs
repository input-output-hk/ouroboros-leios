{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Leios.Conformance.Test where

import Data.Maybe (isJust)
import Test.QuickCheck (
  frequency, Arbitrary (..)
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
  )
 )
import Text.PrettyPrint ((<+>))
import Text.PrettyPrint.HughesPJClass (
  Pretty (pPrint)
 )

import Leios.Conformance.Model (
  EnvAction (..),
  NodeModel(..),
  InputBlock(..),
  EndorserBlock(..),
  Vote(..),
  initialModelState,
  transition
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

instance Arbitrary InputBlock where

instance Arbitrary EndorserBlock where

instance StateModel NetworkModel where
  data Action NetworkModel a where
    Step :: EnvAction -> Action NetworkModel ([InputBlock], [EndorserBlock], [Vote])

  initialState =
    NetworkModel
      { nodeModel = initialModelState
      , initialized = True
      }

  arbitraryAction _ _ =
        fmap (Some . Step) . frequency $
          [(1, pure Tick)]
            ++ fmap (1,) [NewIB <$> arbitrary]
            ++ fmap (1,) [NewEB <$> arbitrary]

  shrinkAction _ _ (Step Tick) = []
  shrinkAction _ _ Step{} = [Some (Step Tick)]

  precondition NetworkModel{nodeModel = s} (Step a) = isJust $ transition s a

  nextState net@NetworkModel{nodeModel = s} (Step a) _ = net{nodeModel = maybe s snd $ transition s a}
