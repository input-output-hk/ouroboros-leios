{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE TupleSections #-}

module Leios.Tracing.Lifecycle (
  lifecycle,
) where

import Control.Concurrent.Chan (Chan, readChan)
import Control.Monad ((<=<))
import Control.Monad.IO.Class (liftIO)
import Control.Monad.State.Strict (StateT, execStateT, gets, modify')
import Data.Aeson (FromJSON (..), Value (Object), withObject, (.:))
import Data.Aeson.Types (Parser, parseMaybe)
import Data.Function (on)
import Data.List (intercalate)
import Data.Map.Strict (Map)
import Data.Monoid (Sum (..))
import Data.Set (Set)
import Data.Text (Text)

import qualified Data.Map.Strict as M (elems, fromList, insertWith, restrictKeys, toList, unionWith)
import qualified Data.Set as S (map, singleton)
import qualified Data.Text as T (unpack)

newtype Earliest a = Earliest {getEarliest :: Maybe a}
  deriving (Show)

instance Eq a => Eq (Earliest a) where
  Earliest (Just x) == Earliest (Just y) = x == y
  Earliest Nothing == Earliest Nothing = True
  _ == _ = False

instance Ord a => Ord (Earliest a) where
  Earliest (Just x) `compare` Earliest (Just y) = x `compare` y
  Earliest (Just _) `compare` Earliest Nothing = LT
  Earliest Nothing `compare` Earliest (Just _) = GT
  Earliest Nothing `compare` Earliest Nothing = EQ

instance Ord a => Semigroup (Earliest a) where
  x <> y = if x < y then x else y

instance Ord a => Monoid (Earliest a) where
  mempty = Earliest Nothing

instance FromJSON a => FromJSON (Earliest a) where
  parseJSON = fmap Earliest . parseJSON

data ItemKey
  = ItemKey
  { kind :: Text
  , item :: Text
  }
  deriving (Eq, Ord, Show)

data ItemInfo
  = ItemInfo
  { size :: Earliest Int
  , references :: Sum Int
  , created :: Earliest Double
  , toIB :: Earliest Double
  , toEB :: Earliest Double
  , toRB :: Earliest Double
  , inRB :: Earliest Double
  , inIBs :: Set Text
  , inEBs :: Set Text
  }
  deriving (Show)

instance Semigroup ItemInfo where
  x <> y =
    ItemInfo
      { size = on (<>) size x y
      , references = on (<>) references x y
      , created = on (<>) created x y
      , toIB = on (<>) toIB x y
      , toEB = on (<>) toEB x y
      , toRB = on (<>) toRB x y
      , inRB = on (<>) inRB x y
      , inIBs = on (<>) inIBs x y
      , inEBs = on (<>) inEBs x y
      }

instance Monoid ItemInfo where
  mempty =
    ItemInfo
      { size = mempty
      , references = mempty
      , created = mempty
      , toIB = mempty
      , toEB = mempty
      , toRB = mempty
      , inRB = mempty
      , inIBs = mempty
      , inEBs = mempty
      }

toCSV :: ItemKey -> ItemInfo -> String
toCSV ItemKey{..} ItemInfo{..} =
  intercalate
    sep
    [ T.unpack kind
    , T.unpack item
    , maybe "NA" show $ getEarliest size
    , show $ getSum references
    , maybe "NA" show $ getEarliest created
    , maybe "NA" show $ getEarliest toIB
    , maybe "NA" show $ getEarliest toEB
    , maybe "NA" show $ getEarliest toRB
    , maybe "NA" show $ getEarliest inRB
    ]

itemHeader :: String
itemHeader =
  intercalate
    sep
    [ "Kind"
    , "Item"
    , "Size [B]"
    , "References"
    , "Created [s]"
    , "To IB [s]"
    , "To EB [s]"
    , "To RB [s]"
    , "In RB [s]"
    ]

sep :: String
sep = ","

parseEvent :: Value -> Parser (ItemKey, ItemInfo, Index)
parseEvent =
  withObject "TraceEvent" $ \event ->
    do
      time <- Earliest <$> event .: "time_s"
      message <- event .: "message"
      typ <- message .: "type"
      ident <- message .: "id"
      parseMessage typ ident time $ Object message

parseMessage :: Text -> Text -> Earliest Double -> Value -> Parser (ItemKey, ItemInfo, Index)
parseMessage "TXGenerated" item created =
  withObject "TXGenerated" $ \message ->
    do
      size <- message .: "size_bytes"
      pure (ItemKey{kind = "TX", item}, mempty{size, created}, mempty)
parseMessage "IBGenerated" item created =
  withObject "IBGenerated" $ \message ->
    do
      size <- message .: "size_bytes"
      txs <- fmap ((,mempty{toIB = created, inIBs = S.singleton item, references = Sum 1}) . ItemKey "TX") <$> message .: "transactions"
      pure (ItemKey{kind = "IB", item}, mempty{size, created}, M.fromList txs)
parseMessage "EBGenerated" item created =
  withObject "EBGenerated" $ \message ->
    do
      size <- message .: "size_bytes"
      ibs <- mapM (fmap ((,mempty{toEB = created, inEBs = S.singleton item, references = Sum 1}) . ItemKey "IB") . (.: "id")) =<< message .: "input_blocks"
      ebs <- mapM (fmap ((,mempty{toEB = created, inEBs = S.singleton item, references = Sum 1}) . ItemKey "EB") . (.: "id")) =<< message .: "endorser_blocks"
      pure (ItemKey{kind = "EB", item}, mempty{size, created}, M.fromList $ ibs <> ebs)
parseMessage "RBGenerated" item created =
  withObject "RBGenerated" $ \message ->
    do
      size <- message .: "size_bytes"
      ebs <-
        maybe
          (pure mempty)
          (fmap (pure . (,mempty{toRB = created, references = Sum 1}) . ItemKey "EB") . (.: "id") <=< (.: "eb"))
          =<< message .: "endorsement"
      txs <- fmap ((,mempty{inRB = created, references = Sum 1}) . ItemKey "TX") <$> message .: "transactions"
      pure (ItemKey{kind = "RB", item}, mempty{size, created}, M.fromList $ ebs <> txs)
parseMessage _ _ _ =
  const $ fail "Ignore"

type Index = Map ItemKey ItemInfo

tally :: Monad m => Value -> StateT Index m ()
tally event =
  case parseMaybe parseEvent event of
    Just (itemKey, itemInfo, updates) ->
      do
        -- Insert the generated items.
        modify' $ M.insertWith (<>) itemKey itemInfo
        -- Update the cross-references.
        modify' $ M.unionWith (<>) updates
    Nothing -> pure ()

updateInclusions :: Monad m => Text -> ItemKey -> Set Text -> StateT Index m ()
updateInclusions kind itemKey includers =
  do
    includers' <- gets $ M.elems . (`M.restrictKeys` S.map (ItemKey kind) includers)
    modify' $
      M.insertWith
        (<>)
        itemKey
        mempty
          { toEB = mconcat $ toEB <$> includers'
          , toRB = mconcat $ toRB <$> includers'
          }

updateEBs :: Monad m => ItemKey -> ItemInfo -> StateT Index m ()
updateEBs itemKey = updateInclusions "EB" itemKey . inEBs

updateIBs :: Monad m => ItemKey -> ItemInfo -> StateT Index m ()
updateIBs itemKey = updateInclusions "IB" itemKey . inIBs

lifecycle :: FilePath -> Chan (Maybe Value) -> IO ()
lifecycle lifecycleFile events =
  do
    let
      go =
        do
          liftIO (readChan events) >>=
            \case
              Nothing -> pure ()
              Just event -> tally event >> go
    index <-
      (`execStateT` mempty) $
        do
          -- Compute the direct metrics from the traces.
          go
          -- Update arrival in EBs and RBs for IBs.
          mapM_ (uncurry updateEBs) =<< gets M.toList
          -- Update arrival in EBs and RBs for TXs.
          mapM_ (uncurry updateIBs) =<< gets M.toList
    writeFile lifecycleFile . unlines . (itemHeader :) $
      uncurry toCSV <$> M.toList index
