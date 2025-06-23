{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}

module Spec.Transition where

import Control.Lens hiding (elements)
import Control.Monad (mzero, replicateM)
import Control.Monad.State
import Data.Default (Default (..))
import Data.Map (Map)
import Data.Set (Set)
import Data.Text (Text)
import Data.Word (Word16, Word64)
import LeiosConfig (leiosStageLengthSlots)
import LeiosEvents
import Test.QuickCheck hiding (scale)
import Prelude hiding (id)

import qualified Data.Map.Strict as M
import qualified Data.Set as S
import qualified Data.Text as T
import qualified Spec.Scenario as Scenario (config, idOther, idSut)

data TracingContext
  = TracingContext
  { _clock :: Time
  , _slotNo :: SlotNo
  , _rbs :: Map Text Text
  , _ibs :: Set Text
  , _ebs :: Set Text
  , _vts :: Set Text
  , _idSut :: Integer
  , _idOther :: Integer
  , _stageLength :: Word
  }
  deriving (Show)

instance Default TracingContext where
  def =
    TracingContext
      0
      0
      mempty
      mempty
      mempty
      mempty
      Scenario.idSut
      Scenario.idOther
      (leiosStageLengthSlots Scenario.config)

clock :: Lens' TracingContext Time
clock = lens _clock $ \ctx x -> ctx{_clock = x}

slotNo :: Lens' TracingContext SlotNo
slotNo = lens _slotNo $ \ctx x -> ctx{_slotNo = x}

rbs :: Lens' TracingContext (Map Text Text)
rbs = lens _rbs $ \ctx x -> ctx{_rbs = x}

ibs :: Lens' TracingContext (Set Text)
ibs = lens _ibs $ \ctx x -> ctx{_ibs = x}

ebs :: Lens' TracingContext (Set Text)
ebs = lens _ebs $ \ctx x -> ctx{_ebs = x}

vts :: Lens' TracingContext (Set Text)
vts = lens _vts $ \ctx x -> ctx{_vts = x}

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

data Transition
  = NextSlot
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
  deriving (Show)

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
    rbs' <- rbs `uses` M.keysSet
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

genEB :: Integer -> StateT TracingContext Gen Text
genEB i =
  do
    slot <- use slotNo
    ebs' <- use ebs
    eb <- lift $ genId i slot ebs'
    ebs %= S.insert eb
    pure eb

genVT :: Integer -> StateT TracingContext Gen Text
genVT i =
  do
    slot <- use slotNo
    vts' <- use vts
    vt <- lift $ genId i slot vts'
    vts %= S.insert vt
    pure vt

tick :: StateT TracingContext Gen ()
tick = clock %= (+ 0.000001)

transition :: Transition -> StateT TracingContext Gen [Event]
transition SkipSlot =
  do
    slotNo %= (+ 1)
    pure mempty
transition NextSlot =
  do
    event <- Slot <$> use sut <*> use slotNo
    slotNo %= (+ 1)
    pure [event]
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
    sender <- other `uses` pure
    recipient <- use sut
    let block_ids = mzero
    msg_size_bytes <- lift arbitrary
    sending_s <- clock `uses` pure
    (block_id, _) <- genRB =<< use idOther
    pure [RBReceived{..}]
transition SkipIB =
  fmap pure . NoIBGenerated <$> use sut <*> use slotNo
transition GenerateIB =
  do
    tick
    slot <- use slotNo
    producer <- use sut
    pipeline <- uses stageLength $ (slot `div`) . fromIntegral
    id <- genIB =<< use idSut
    size_bytes <- lift arbitrary
    payload_bytes <- lift arbitrary
    rb_ref <- lift . fmap pure . elements . M.keys =<< use rbs
    pure [IBGenerated{..}]
transition ReceiveIB =
  do
    tick
    sender <- other `uses` pure
    recipient <- use sut
    let block_ids = mzero
    msg_size_bytes <- lift arbitrary
    sending_s <- clock `uses` pure
    block_id <- genIB =<< use idOther
    pure [IBReceived{..}]
transition SkipEB =
  fmap pure . NoEBGenerated <$> use sut <*> use slotNo
transition GenerateEB =
  do
    tick
    slot <- use slotNo
    producer <- use sut
    id <- genEB =<< use idSut
    pipeline <- uses stageLength $ (slot `div`) . fromIntegral
    bytes <- lift arbitrary
    input_blocks <- lift . sublistOf =<< uses ibs (fmap BlockRef . S.toList)
    endorser_blocks <- lift . sublistOf =<< uses ebs (fmap BlockRef . S.toList)
    pure [EBGenerated{..}]
transition ReceiveEB =
  do
    tick
    sender <- other `uses` pure
    recipient <- use sut
    let block_ids = mzero
    msg_size_bytes <- lift arbitrary
    sending_s <- clock `uses` pure
    block_id <- genEB =<< use idOther
    pure [EBReceived{..}]
transition SkipVT =
  fmap pure . NoVTBundleGenerated <$> use sut <*> use slotNo
transition GenerateVT =
  do
    tick
    slot <- use slotNo
    producer <- use sut
    id <- genVT =<< use idSut
    pipeline <- uses stageLength $ (slot `div`) . fromIntegral
    bytes <- lift arbitrary
    voted <- lift . sublistOf =<< uses ebs S.toList
    cast <- lift $ replicateM (length voted) arbitrary
    let votes = M.fromList $ zip voted cast
    pure [VTBundleGenerated{..}]
transition ReceiveVT =
  do
    tick
    sender <- other `uses` pure
    recipient <- use sut
    let block_ids = mzero
    msg_size_bytes <- lift arbitrary
    sending_s <- clock `uses` pure
    block_id <- genVT =<< use idOther
    pure [VTBundleReceived{..}]

transitions :: [Transition] -> Gen [TraceEvent]
transitions =
  (`evalStateT` def)
    . (mapM timestamp =<<)
    . fmap concat
    . mapM transition

timestamp :: Monad m => Event -> StateT TracingContext m TraceEvent
timestamp = uses clock . flip TraceEvent
