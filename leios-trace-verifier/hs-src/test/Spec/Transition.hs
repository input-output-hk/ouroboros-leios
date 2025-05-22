{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}

module Spec.Transition where

import Control.Lens hiding (_1, _2, elements)
import Control.Monad (mzero)
import Control.Monad.State
import Data.Default (Default(..))
import Data.Map (Map)
import Data.Word (Word16, Word64)
import Data.Set (Set)
import Data.Text (Text)
import LeiosConfig (leiosStageLengthSlots)
import LeiosEvents
import Prelude hiding (id)
import Test.QuickCheck hiding (scale)

import qualified Data.Map.Strict as M
import qualified Data.Set as S
import qualified Data.Text as T
import qualified Spec.Scenario as Scenario (config, idOther, idSut)

data TracingContext =
  TracingContext
  {
    _clock :: Time
  , _slotNo :: SlotNo
  , _rbs :: Map Text Text
  , _ibs :: Set Text
  , _ebs :: Set Text
  , _votes :: Set Text
  , _idSut :: Integer
  , _idOther :: Integer
  , _stageLength :: Word
  }
    deriving Show

instance Default TracingContext where
  def =
    TracingContext
      0 0 mempty mempty mempty mempty
      Scenario.idSut Scenario.idOther
      (leiosStageLengthSlots Scenario.config)

clock :: Lens' TracingContext Time
clock = lens _clock $ \ctx x -> ctx {_clock = x}

slotNo:: Lens' TracingContext SlotNo
slotNo= lens _slotNo $ \ctx x -> ctx {_slotNo = x}

rbs :: Lens' TracingContext (Map Text Text)
rbs = lens _rbs $ \ctx x -> ctx {_rbs = x}

ibs :: Lens' TracingContext (Set Text)
ibs = lens _ibs $ \ctx x -> ctx {_ibs = x}

ebs :: Lens' TracingContext (Set Text)
ebs = lens _ebs $ \ctx x -> ctx {_ebs = x}

votes :: Lens' TracingContext (Set Text)
votes = lens _votes $ \ctx x -> ctx {_votes = x}

idSut :: Getter TracingContext Integer
idSut = to _idSut

idOther :: Getter TracingContext Integer
idOther = to _idOther

sut :: Getter TracingContext Text
sut = to $ T.pack . ("node-" <>) . show . _idSut

other :: Getter TracingContext Text
other = to $ T.pack . ("node-" <>) . show . _idOther

stageLength :: Getter TracingContext Word
stageLength = to _stageLength

data Transition =
    NextSlot
  | SkipSlot
  | GenerateRB
  | ReceiveRB
  | GenerateIB
  | SkipIB
  | ReceiveIB
  | GenerateEB
  | SkipEB
  | ReceiveEB
  | GenerateVT
  | SkipVT
  | ReceiveVT
  deriving Show

genId :: Integer -> Word64 -> Set Text -> Gen Text
genId system slot forbidden =
  let
    g = T.pack . ((show system <> "-" <> show slot <> "-") <>) . show <$> (arbitrary :: Gen Word16)
  in
    g `suchThat` (not . (`S.member` forbidden))

genRB :: Integer -> StateT TracingContext Gen (Text, Nullable BlockRef)
genRB i =
  do
    slot <- use slotNo
    rbs' <- M.keysSet <$> use rbs
    block_id <- lift $ genId i slot rbs'
    parent <-
      if S.null rbs'
        then pure "genesis"
        else lift . elements $ S.toList rbs'
    rbs %= M.insert block_id parent
    pure (block_id, Nullable . pure $ BlockRef parent)

genIB :: Integer -> StateT TracingContext Gen Text
genIB i =
  do
    slot <- use slotNo
    ibs' <- use ibs
    ib <- lift $ genId i slot ibs'
    ibs %= S.insert ib
    pure ib

tick :: StateT TracingContext Gen ()
tick = clock %= (+ 0.000001)

transition :: Transition -> StateT TracingContext Gen [Event]
transition NextSlot =
  do
    event <- Slot <$> use sut <*> use slotNo
    slotNo %= (+ 1)
    pure [event]
transition SkipSlot =
  do
    slotNo %= (+ 1)
    pure mempty
transition GenerateRB =
  do
    tick
    producer <- use sut
    let endorsement = Nullable mzero
        endorsements = mzero
    slot <- use slotNo
    (block_id, parent) <- genRB =<< use idSut
    size_bytes <- lift arbitrary
    payload_bytes <- lift arbitrary
    pure [RBGenerated{..}]
transition ReceiveRB =
  do
    tick
    sender <- pure <$> use other
    recipient <- use sut
    let block_ids = mzero
    msg_size_bytes <- lift arbitrary
    sending_s <- pure <$> use clock
    (block_id, _) <- genRB =<< use idOther
    pure [RBReceived{..}]
transition GenerateIB =
  do
    tick
    slot <- use slotNo
    producer <- use sut
    pipeline <- (slot `div`) . fromIntegral <$> use stageLength
    id <- genIB =<< use idSut
    size_bytes <- lift arbitrary
    payload_bytes <- lift arbitrary
    rb_ref <- lift . fmap pure . elements . M.keys =<< use rbs
    pure [IBGenerated{..}]
transition SkipIB = fmap pure . NoIBGenerated <$> use sut <*> use slotNo
transition ReceiveIB =
  do
    tick
    sender <- pure <$> use other
    recipient <- use sut
    let block_ids = mzero
    msg_size_bytes <- lift arbitrary
    sending_s <- pure <$> use clock
    block_id <- genIB =<< use idOther
    pure [IBReceived{..}]
transition SkipEB = fmap pure . NoEBGenerated <$> use sut <*> use slotNo
transition SkipVT = fmap pure . NoVTBundleGenerated <$> use sut <*> use slotNo
transition _ = undefined

transitions :: [Transition] -> Gen [TraceEvent]
transitions =
  (`evalStateT` def)
    . (mapM timestamp =<<)
    . fmap concat
    . mapM transition

timestamp :: Monad m => Event -> StateT TracingContext m TraceEvent
timestamp = (<$> use clock) . flip TraceEvent
