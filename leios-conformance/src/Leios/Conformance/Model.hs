{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Leios.Conformance.Model (
  module Leios.Conformance.Model,
  module Lib,
) where

import Data.Aeson (FromJSON (..), ToJSON (..))
import Data.Maybe (maybeToList)
import GHC.Generics (Generic)
import Text.PrettyPrint.HughesPJClass (Pretty (pPrint))

import Lib

data EnvAction
  = Tick
  | NewIB InputBlock
  | NewEB EndorserBlock
  | NewVote Vote
  deriving (Eq, Show)

instance FromJSON IBHeader
instance FromJSON IBBody
instance FromJSON InputBlock

instance ToJSON IBHeader
instance ToJSON IBBody
instance ToJSON InputBlock

instance Pretty InputBlock where
  pPrint (InputBlock{}) = "InputBlock"

instance FromJSON EndorserBlock
instance ToJSON EndorserBlock
instance Pretty EndorserBlock where
  pPrint (EndorserBlock{}) = "EndorserBlock"

type Vote = () -- TODO: use Vote extracted from Agda
type NodeModel = LeiosState

initialModelState :: NodeModel
initialModelState =
  LeiosState
    { v = ()
    , sD = MkHSMap []
    , fFDState = ()
    , ledger = []
    , toPropose = []
    , iBs = []
    , eBs = []
    , vs = []
    , slot = 0
    , iBHeaders = []
    , iBBodies = []
    , upkeep = MkHSSet []
    , baseState = ()
    , votingState = ()
    }

-- TODO
makeIB :: NodeModel -> Maybe InputBlock
makeIB _ = Nothing

-- TODO
makeEB :: NodeModel -> Maybe EndorserBlock
makeEB _ = Nothing

-- TODO
makeVote :: NodeModel -> Maybe Vote
makeVote _ = Nothing

addIB :: InputBlock -> NodeModel -> NodeModel
addIB ib nm@LeiosState{..} = nm{iBs = ib : iBs}

addEB :: EndorserBlock -> NodeModel -> NodeModel
addEB eb nm@LeiosState{..} = nm{eBs = eb : eBs}

addVote :: Vote -> NodeModel -> NodeModel
addVote x nm@LeiosState{..} = nm{vs = [x] : vs}

-- TODO: Leios executable specification
transition :: NodeModel -> EnvAction -> Maybe (([InputBlock], [EndorserBlock], [Vote]), NodeModel)
transition nm Tick = do
  -- TODO: guards
  let ibs = maybeToList (makeIB nm)
      ebs = maybeToList (makeEB nm)
      votes = maybeToList (makeVote nm)
  pure ((ibs, ebs, votes), nm)
transition nm (NewIB ib) = do
  -- TODO: guards
  pure (([], [], []), addIB ib nm)
transition nm (NewEB eb) = do
  -- TODO: guards
  pure (([], [], []), addEB eb nm)
transition nm (NewVote v) = do
  -- TODO: guards
  pure (([], [], []), addVote v nm)
