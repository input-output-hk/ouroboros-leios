{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Bytes where

import Data.Aeson (FromJSON (..), FromJSONKey (..), FromJSONKeyFunction (..), ToJSON, ToJSONKey, withText)
import qualified Data.Aeson as A
import Data.Aeson.Types (ToJSON (..), ToJSONKey (..), parseFail, toJSONKeyText)
import qualified Data.ByteString as BS
import qualified Data.ByteString.Base16 as B16
import qualified Data.ByteString.Char8 as BS8
import Data.String (IsString (..))
import qualified Data.Text as T
import Text.Read (Read (..))

newtype Bytes where
  Bytes :: {getBytes :: BS.ByteString} -> Bytes
  deriving (Eq, Ord)

instance Read Bytes where
  readPrec = do
    Right bs' <- B16.decode . BS8.pack <$> readPrec
    pure $ Bytes bs'

instance Show Bytes where
  show = show . BS8.unpack . B16.encode . getBytes

instance IsString Bytes where
  fromString s = either (\e -> error $ "failed to read: " <> s <> ", " <> e) Bytes $ B16.decode $ BS8.pack s

instance FromJSON Bytes where
  parseJSON = withText "Base 16 Bytes" $ either parseFail (pure . Bytes) . B16.decode . BS8.pack . T.unpack

instance ToJSON Bytes where
  toJSON = A.String . T.pack . init . tail . show

instance FromJSONKey Bytes where
  fromJSONKey = FromJSONKeyTextParser $ \t ->
    case B16.decode . BS8.pack . T.unpack $ t of
      Left err -> fail err
      Right k -> pure $ Bytes k

instance ToJSONKey Bytes where
  toJSONKey = toJSONKeyText $ T.pack . init . tail . show

deriving via Bytes instance FromJSON BS.ByteString
deriving via Bytes instance ToJSON BS.ByteString
