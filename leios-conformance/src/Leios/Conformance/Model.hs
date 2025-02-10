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
import Data.List ((\\))
import Data.Maybe (maybeToList)
import GHC.Generics (Generic)
import Lib
import Text.PrettyPrint (braces, hang, text, vcat, (<+>))
import Text.PrettyPrint.HughesPJClass (
  Pretty (pPrint, pPrintPrec),
  maybeParens,
  prettyNormal,
 )
import Data.Text.Internal (Text)

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
  pPrint (InputBlock{header = IBHeader s p, body = IBBody{..}}) =
    hang "InputBlock" 2 $
      braces $
        vcat
          [ hang "slot number =" 2 $ pPrint s
          , hang "producer Id =" 2 $ pPrint p
          , hang "transactions =" 2 $ pPrint txs
          ]

instance FromJSON EndorserBlock
instance ToJSON EndorserBlock

instance Pretty EndorserBlock where
  pPrint (EndorserBlock s p ibs) =
    hang "EndorserBlock" 2 $
      braces $
        vcat
          [ hang "slot number =" 2 $ pPrint s
          , hang "producer Id =" 2 $ pPrint p
          , hang "IB refs=" 2 $ pPrint ibs
          ]

type Vote = () -- TODO: use Vote extracted from Agda
type NodeModel = LeiosState

initialModelState :: NodeModel
initialModelState =
  LeiosState
    { v = ()
    , sD = MkHSMap [(0, 1)]
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

makeStep' :: LeiosState -> ComputationResult Text (LeiosOutput, LeiosState)
makeStep' = flip step I_SLOT

makeStep :: NodeModel -> Maybe NodeModel
makeStep nm =
  case makeStep' nm of
    Success (_, s) -> Just s
    Failure _ -> Nothing

addIB :: InputBlock -> NodeModel -> NodeModel
addIB ib nm@LeiosState{..} = nm{iBs = ib : iBs}

addEB :: EndorserBlock -> NodeModel -> NodeModel
addEB eb nm@LeiosState{..} = nm{eBs = eb : eBs}

addVote :: Vote -> NodeModel -> NodeModel
addVote x nm@LeiosState{..} = nm{vs = [x] : vs}

-- TODO: Leios executable specification
transition :: NodeModel -> EnvAction -> Maybe (([InputBlock], [EndorserBlock], [[Vote]]), NodeModel)
transition s Tick = do
  -- TODO: guards
  s' <- makeStep s
  let ffd = fFDState s
  let ffd' = fFDState s'
  pure (([],[],[]), s) -- FIXME: return blocks from FFD
transition nm (NewIB ib) = do
  -- TODO: guards
  pure (([], [], []), addIB ib nm)
transition nm (NewEB eb) = do
  -- TODO: guards
  pure (([], [], []), addEB eb nm)
transition nm (NewVote v) = do
  -- TODO: guards
  pure (([], [], []), addVote v nm)
