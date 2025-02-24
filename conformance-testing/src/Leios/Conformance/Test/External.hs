{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module Leios.Conformance.Test.External where

import Control.Monad (unless, when)
import Control.Monad.IO.Class ()
import Control.Monad.State (
  MonadState (get),
  MonadTrans (lift),
  StateT,
  modify,
 )
import Data.Aeson (FromJSON, ToJSON)
import Data.Aeson qualified as A
import Data.ByteString.Char8 qualified as BS8
import Data.ByteString.Lazy qualified as LBS
import Data.ByteString.Lazy.Char8 qualified as LBS8
import Data.Default (Default (def))
import GHC.Generics (Generic)
import System.IO (Handle)
import Test.QuickCheck (
  Blind (Blind),
  Property,
  counterexample,
  ioProperty,
  noShrinking,
 )
import Test.QuickCheck.Extras (runPropertyStateT)
import Test.QuickCheck.Monadic (monadicIO, monitor)
import Test.QuickCheck.StateModel (
  Actions,
  Realized,
  RunModel (perform, postcondition),
  counterexamplePost,
  monitorPost,
  runActions,
 )

import Text.PrettyPrint ((<+>))
import Text.PrettyPrint.HughesPJClass (Pretty (pPrint))

import Prelude hiding (round)

import Leios.Conformance.Model
import Leios.Conformance.Test

data NodeRequest
  = Initialize
  | NewSlot
      { newIBs :: [InputBlock]
      , newEBs :: [EndorserBlock]
      , newVotes :: [[Vote]]
      }
  | Stop
  deriving (Eq, Generic, Show)

instance FromJSON NodeRequest
instance ToJSON NodeRequest

data NodeResponse
  = NodeResponse
      { diffuseIBs :: [InputBlock]
      , diffuseEBs :: [EndorserBlock]
      , diffuseVotes :: [[Vote]]
      }
  | Failed
      { failure :: String
      }
  | Stopped
  deriving (Eq, Generic, Show)

instance Default NodeResponse where
  def = NodeResponse mempty mempty mempty

instance FromJSON NodeResponse
instance ToJSON NodeResponse

data RunState = RunState
  { hReader :: Handle
  , hWriter :: Handle
  , unfetchedIBs :: [InputBlock]
  , unfetchedEBs :: [EndorserBlock]
  , unfetchedVotes :: [[Vote]]
  }

callSUT :: RunState -> NodeRequest -> IO NodeResponse
callSUT RunState{hReader, hWriter} req =
  do
    LBS8.hPutStrLn hWriter $ A.encode req
    either Failed id . A.eitherDecode' . LBS.fromStrict <$> BS8.hGetLine hReader

type Runtime = StateT RunState IO

instance Realized IO ([InputBlock], [EndorserBlock], [[Vote]]) ~ ([InputBlock], [EndorserBlock], [[Vote]]) => RunModel NetworkModel Runtime where
  perform NetworkModel{nodeModel = LeiosState{}} (Step a) _ = case a of
    Tick -> do
      rs@RunState{..} <- get
      modify $ \rs' -> rs'{unfetchedIBs = mempty, unfetchedEBs = mempty, unfetchedVotes = mempty}
      lift
        ( callSUT
            rs
            NewSlot
              { newIBs = unfetchedIBs
              , newEBs = unfetchedEBs
              , newVotes = unfetchedVotes
              }
        )
        >>= \case
          NodeResponse{..} -> pure (diffuseIBs, diffuseEBs, diffuseVotes)
          _ -> pure (mempty, mempty, mempty) -- FIXME: The state model should define an error type.
    NewIB ib -> do
      modify $ \rs -> rs{unfetchedIBs = unfetchedIBs rs ++ pure ib}
      pure (mempty, mempty, mempty)
    NewEB eb -> do
      modify $ \rs -> rs{unfetchedEBs = unfetchedEBs rs ++ pure eb}
      pure (mempty, mempty, mempty)
    NewVote x -> do
      modify $ \rs -> rs{unfetchedVotes = unfetchedVotes rs ++ pure [x]}
      pure (mempty, mempty, mempty)

  postcondition (NetworkModel{nodeModel = s}, NetworkModel{nodeModel = s'}) (Step a) _ (ibs, ebs, votes) = do
    let (expectedIBs, expectedEBs, expectedVotes) = maybe (mempty, mempty, mempty) fst $ transition s a
    let ok = (ibs, ebs) == (expectedIBs, expectedEBs)
    monitorPost . counterexample . show $ "  action $" <+> pPrint a
    when (a == Tick && slot s + 1 /= slot s') $
      monitorPost . counterexample $
        "  -- new slot: " ++ show (slot s')
    unless (null ibs) $
      monitorPost . counterexample . show $
        "  --      got InputBlocks:" <+> pPrint ibs
    when (ibs /= expectedIBs) $
      counterexamplePost . show $
        "  -- expected InputBlocks:" <+> pPrint expectedIBs
    unless (null ebs) $
      monitorPost . counterexample . show $
        "  --      got EndorserBlocks:" <+> pPrint ebs
    when (ebs /= expectedEBs) $
      counterexamplePost . show $
        "  -- expected EndorserBlocks:" <+> pPrint expectedEBs
    unless (null votes) $
      monitorPost . counterexample . show $
        "  --      got Votes:" <+> pPrint votes
    when (votes /= expectedVotes) $
      counterexamplePost . show $
        "  -- expected Votes:" <+> pPrint expectedVotes
    pure ok

prop_node :: Handle -> Handle -> Blind (Actions NetworkModel) -> Property
prop_node hReader hWriter (Blind as) = noShrinking $
  ioProperty $ do
    let unfetchedIBs = mempty
        unfetchedEBs = mempty
        unfetchedVotes = mempty
    callSUT
      RunState{..}
      Initialize
      >>= \case
        NodeResponse{} ->
          pure $
            monadicIO $ do
              monitor $ counterexample "-- Actions:"
              monitor $ counterexample "do"
              _ <- runPropertyStateT (runActions @_ @Runtime as) RunState{..}
              pure True
        _ -> pure $ monadicIO $ pure False
