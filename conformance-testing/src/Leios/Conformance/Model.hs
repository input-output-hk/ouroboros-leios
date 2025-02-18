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
import Data.Text (unpack)
import Data.Text.Internal (Text (..))
import Lib
import Text.PrettyPrint (braces, hang, vcat)
import Text.PrettyPrint.HughesPJClass (
  Pretty (pPrint),
 )

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

instance Pretty Text where
  pPrint = pPrint . unpack

instance Pretty InputBlock where
  pPrint (InputBlock{header = IBHeader s p hb, body = IBBody{..}}) =
    hang "InputBlock" 2 $
      braces $
        vcat
          [ hang "slot number =" 2 $ pPrint s
          , hang "producer Id =" 2 $ pPrint p
          , hang "body hash =" 2 $ pPrint hb
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
    , sD = MkHSMap [(0, 45000000000000000)]
    , fFDState = FFDState [] [] [] [] [] []
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

makeTx :: LeiosState -> ComputationResult Text (LeiosOutput, LeiosState)
makeTx = flip step (I_SUBMIT (Right [0 .. 10])) -- FIXME: where to get txs from

makeStep' :: LeiosState -> ComputationResult Text (LeiosOutput, LeiosState)
makeStep' = flip step I_SLOT

makeStep :: NodeModel -> Maybe NodeModel
makeStep nm =
  case makeStep' nm of
    Success (_, s) -> Just s
    Failure _ -> Nothing

addIB :: InputBlock -> NodeModel -> NodeModel
addIB ib nm@LeiosState{..} = nm{fFDState = fFDState{inIBs = ib : inIBs fFDState}}

addEB :: EndorserBlock -> NodeModel -> NodeModel
addEB eb nm@LeiosState{..} = nm{fFDState = fFDState{inEBs = eb : inEBs fFDState}}

addVote :: Vote -> NodeModel -> NodeModel
addVote x nm@LeiosState{..} = nm{fFDState = fFDState{inVTs = [x] : inVTs fFDState}}

-- TODO: export from Agda
transition :: NodeModel -> EnvAction -> Maybe (([InputBlock], [EndorserBlock], [[Vote]]), NodeModel)
transition s Tick = do
  -- TODO: guards
  let ffd = fFDState s
  s' <- makeStep (s{toPropose = [0 .. 10]}) -- FIXME: see makeTx above
  let ffd' = fFDState s'
  pure ((outIBs ffd' \\ outIBs ffd, outEBs ffd' \\ outEBs ffd, outVTs ffd' \\ outVTs ffd), s')
transition nm (NewIB ib) = do
  -- TODO: guards
  pure (([], [], []), addIB ib nm)
transition nm (NewEB eb) = do
  -- TODO: guards
  pure (([], [], []), addEB eb nm)
transition nm (NewVote v) = do
  -- TODO: guards
  pure (([], [], []), addVote v nm)
