{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeApplications #-}

module LeiosProtocol.Config where

import Data.Aeson (Options (allNullaryToStringTag), defaultOptions, genericToEncoding, genericToJSON)
import Data.Aeson.Encoding (pairs)
import Data.Aeson.Types (Encoding, FromJSON (..), KeyValue ((.=)), Options (constructorTagModifier), Parser, ToJSON (..), Value (..), genericParseJSON, object, typeMismatch, withObject, (.:))
import Data.Default (Default (..))
import Data.Maybe (catMaybes)
import Data.Text (Text)
import Data.Word
import Data.Yaml (ParseException)
import qualified Data.Yaml as Yaml
import GHC.Exception (displayException)
import GHC.Generics (Generic)
import JSONCompat (Getter, always, camelToKebab, get, omitDefault, parseFieldOrDefault)
import System.Exit (exitFailure)
import System.IO (hPutStrLn, stderr)

newtype SizeBytes = SizeBytes {unSizeBytes :: Word}
  deriving newtype (Show, Eq, Ord, FromJSON, ToJSON, Num, Real, Enum, Integral)

newtype DurationMs = DurationMs {unDurationMs :: Double}
  deriving newtype (Show, Eq, Ord, FromJSON, ToJSON, Num, Real, RealFrac, Fractional)

-- | Probability distributions.
data Distribution
  = Normal {mean :: Double, std_dev :: Double}
  | Exp {lambda :: Double, scale :: Maybe Double}
  | LogNormal {mu :: Double, sigma :: Double}
  deriving (Show, Eq, Generic)

data DiffusionStrategy
  = -- | use same order as relay peer
    PeerOrder
  | -- | request message with highest slot
    FreshestFirst
  | -- | request message with lowest slot
    OldestFirst
  deriving (Show, Eq, Generic)

data RelayStrategy
  = RequestFromFirst
  | RequestFromAll
  deriving (Show, Eq, Generic)

data Config = Config
  { relayStrategy :: RelayStrategy
  , tcpCongestionControl :: Bool
  , multiplexMiniProtocols :: Bool
  , treatBlocksAsFull :: Bool
  , leiosStageLengthSlots :: Word
  , leiosStageActiveVotingSlots :: Word
  , leiosVoteSendRecvStages :: Bool
  , txGenerationDistribution :: Distribution
  , txSizeBytesDistribution :: Distribution
  , txValidationCpuTimeMs :: DurationMs
  , txMaxSizeBytes :: SizeBytes
  , rbGenerationProbability :: Double
  , rbGenerationCpuTimeMs :: DurationMs
  , rbHeadValidationCpuTimeMs :: DurationMs
  , rbHeadSizeBytes :: SizeBytes
  , rbBodyMaxSizeBytes :: SizeBytes
  , rbBodyLegacyPraosPayloadValidationCpuTimeMsConstant :: DurationMs
  , rbBodyLegacyPraosPayloadValidationCpuTimeMsPerByte :: DurationMs
  , rbBodyLegacyPraosPayloadAvgSizeBytes :: SizeBytes
  , ibGenerationProbability :: Double
  , ibGenerationCpuTimeMs :: DurationMs
  , ibHeadSizeBytes :: SizeBytes
  , ibHeadValidationCpuTimeMs :: DurationMs
  , ibBodyValidationCpuTimeMsConstant :: DurationMs
  , ibBodyValidationCpuTimeMsPerByte :: DurationMs
  , ibBodyMaxSizeBytes :: SizeBytes
  , ibBodyAvgSizeBytes :: SizeBytes
  , ibDiffusionStrategy :: DiffusionStrategy
  , ibDiffusionMaxWindowSize :: Word16
  , ibDiffusionMaxHeadersToRequest :: Word16
  , ibDiffusionMaxBodiesToRequest :: Word16
  , ebGenerationProbability :: Double
  , ebGenerationCpuTimeMs :: DurationMs
  , ebValidationCpuTimeMs :: DurationMs
  , ebSizeBytesConstant :: SizeBytes
  , ebSizeBytesPerIb :: SizeBytes
  , ebDiffusionStrategy :: DiffusionStrategy
  , ebDiffusionMaxWindowSize :: Word16
  , ebDiffusionMaxHeadersToRequest :: Word16
  , ebDiffusionMaxBodiesToRequest :: Word16
  , voteGenerationProbability :: Double
  , voteGenerationCpuTimeMsConstant :: DurationMs
  , voteGenerationCpuTimeMsPerIb :: DurationMs
  , voteValidationCpuTimeMs :: DurationMs
  , voteThreshold :: Word
  , voteBundleSizeBytesConstant :: SizeBytes
  , voteBundleSizeBytesPerEb :: SizeBytes
  , voteDiffusionStrategy :: DiffusionStrategy
  , voteDiffusionMaxWindowSize :: Word16
  , voteDiffusionMaxHeadersToRequest :: Word16
  , voteDiffusionMaxBodiesToRequest :: Word16
  , certGenerationCpuTimeMsConstant :: DurationMs
  , certGenerationCpuTimeMsPerNode :: DurationMs
  , certValidationCpuTimeMsConstant :: DurationMs
  , certValidationCpuTimeMsPerNode :: DurationMs
  , certSizeBytesConstant :: SizeBytes
  , certSizeBytesPerNode :: SizeBytes
  }
  deriving (Eq, Show, Generic)

instance Default Config where
  def :: Config
  def =
    Config
      { relayStrategy = RequestFromFirst
      , tcpCongestionControl = True
      , multiplexMiniProtocols = True
      , treatBlocksAsFull = False
      , leiosStageLengthSlots = 20
      , leiosStageActiveVotingSlots = 1
      , leiosVoteSendRecvStages = False
      , txGenerationDistribution = Exp{lambda = 0.85, scale = Just 1000}
      , txSizeBytesDistribution = LogNormal{mu = 6.833, sigma = 1.127}
      , txValidationCpuTimeMs = 1.5
      , txMaxSizeBytes = 16384
      , rbGenerationProbability = 5.0e-2
      , rbGenerationCpuTimeMs = 1.0
      , rbHeadValidationCpuTimeMs = 1.0
      , rbHeadSizeBytes = 1024
      , rbBodyMaxSizeBytes = 90112
      , rbBodyLegacyPraosPayloadValidationCpuTimeMsConstant = 50.0
      , rbBodyLegacyPraosPayloadValidationCpuTimeMsPerByte = 0.0005
      , rbBodyLegacyPraosPayloadAvgSizeBytes = 0
      , ibGenerationProbability = 5
      , ibGenerationCpuTimeMs = 130.0
      , ibHeadSizeBytes = 304
      , ibHeadValidationCpuTimeMs = 1.0
      , ibBodyValidationCpuTimeMsConstant = 50.0
      , ibBodyValidationCpuTimeMsPerByte = 0.0005
      , ibBodyMaxSizeBytes = 327680
      , ibBodyAvgSizeBytes = 102400
      , ibDiffusionStrategy = FreshestFirst
      , ibDiffusionMaxWindowSize = 100
      , ibDiffusionMaxHeadersToRequest = 100
      , ibDiffusionMaxBodiesToRequest = 1
      , ebGenerationProbability = 1.5
      , ebGenerationCpuTimeMs = 75.0
      , ebValidationCpuTimeMs = 1.0
      , ebSizeBytesConstant = 32
      , ebSizeBytesPerIb = 32
      , ebDiffusionStrategy = PeerOrder
      , ebDiffusionMaxWindowSize = 100
      , ebDiffusionMaxHeadersToRequest = 100
      , ebDiffusionMaxBodiesToRequest = 1
      , voteGenerationProbability = 500.0
      , voteGenerationCpuTimeMsConstant = 0.164
      , voteGenerationCpuTimeMsPerIb = 0.0
      , voteValidationCpuTimeMs = 0.816
      , voteThreshold = 300
      , voteBundleSizeBytesConstant = 0
      , voteBundleSizeBytesPerEb = 105
      , voteDiffusionStrategy = PeerOrder
      , voteDiffusionMaxWindowSize = 100
      , voteDiffusionMaxHeadersToRequest = 100
      , voteDiffusionMaxBodiesToRequest = 1
      , certGenerationCpuTimeMsConstant = 90.0
      , certGenerationCpuTimeMsPerNode = 0.0
      , certValidationCpuTimeMsConstant = 130.0
      , certValidationCpuTimeMsPerNode = 0.0
      , certSizeBytesConstant = 136
      , certSizeBytesPerNode = 15
      }

configToJSONWith :: Getter Config -> Config -> Value
configToJSONWith getter = object . configToKVsWith getter

configToEncodingWith :: Getter Config -> Config -> Encoding
configToEncodingWith getter = pairs . mconcat . configToKVsWith getter

configToKVsWith :: KeyValue e kv => Getter Config -> Config -> [kv]
configToKVsWith getter cfg =
  catMaybes
    [ get @"relayStrategy" getter cfg
    , get @"tcpCongestionControl" getter cfg
    , get @"multiplexMiniProtocols" getter cfg
    , get @"treatBlocksAsFull" getter cfg
    , get @"leiosStageLengthSlots" getter cfg
    , get @"leiosStageActiveVotingSlots" getter cfg
    , get @"leiosVoteSendRecvStages" getter cfg
    , get @"txGenerationDistribution" getter cfg
    , get @"txSizeBytesDistribution" getter cfg
    , get @"txValidationCpuTimeMs" getter cfg
    , get @"txMaxSizeBytes" getter cfg
    , get @"rbGenerationProbability" getter cfg
    , get @"rbGenerationCpuTimeMs" getter cfg
    , get @"rbHeadValidationCpuTimeMs" getter cfg
    , get @"rbHeadSizeBytes" getter cfg
    , get @"rbBodyMaxSizeBytes" getter cfg
    , get @"rbBodyLegacyPraosPayloadValidationCpuTimeMsConstant" getter cfg
    , get @"rbBodyLegacyPraosPayloadValidationCpuTimeMsPerByte" getter cfg
    , get @"rbBodyLegacyPraosPayloadAvgSizeBytes" getter cfg
    , get @"ibGenerationProbability" getter cfg
    , get @"ibGenerationCpuTimeMs" getter cfg
    , get @"ibHeadSizeBytes" getter cfg
    , get @"ibHeadValidationCpuTimeMs" getter cfg
    , get @"ibBodyValidationCpuTimeMsConstant" getter cfg
    , get @"ibBodyValidationCpuTimeMsPerByte" getter cfg
    , get @"ibBodyMaxSizeBytes" getter cfg
    , get @"ibBodyAvgSizeBytes" getter cfg
    , get @"ibDiffusionStrategy" getter cfg
    , get @"ibDiffusionMaxWindowSize" getter cfg
    , get @"ibDiffusionMaxHeadersToRequest" getter cfg
    , get @"ibDiffusionMaxBodiesToRequest" getter cfg
    , get @"ebGenerationProbability" getter cfg
    , get @"ebGenerationCpuTimeMs" getter cfg
    , get @"ebValidationCpuTimeMs" getter cfg
    , get @"ebSizeBytesConstant" getter cfg
    , get @"ebSizeBytesPerIb" getter cfg
    , get @"ebDiffusionStrategy" getter cfg
    , get @"ebDiffusionMaxWindowSize" getter cfg
    , get @"ebDiffusionMaxHeadersToRequest" getter cfg
    , get @"ebDiffusionMaxBodiesToRequest" getter cfg
    , get @"voteGenerationProbability" getter cfg
    , get @"voteGenerationCpuTimeMsConstant" getter cfg
    , get @"voteGenerationCpuTimeMsPerIb" getter cfg
    , get @"voteValidationCpuTimeMs" getter cfg
    , get @"voteThreshold" getter cfg
    , get @"voteBundleSizeBytesConstant" getter cfg
    , get @"voteBundleSizeBytesPerEb" getter cfg
    , get @"voteDiffusionStrategy" getter cfg
    , get @"voteDiffusionMaxWindowSize" getter cfg
    , get @"voteDiffusionMaxHeadersToRequest" getter cfg
    , get @"voteDiffusionMaxBodiesToRequest" getter cfg
    , get @"certGenerationCpuTimeMsConstant" getter cfg
    , get @"certGenerationCpuTimeMsPerNode" getter cfg
    , get @"certValidationCpuTimeMsConstant" getter cfg
    , get @"certValidationCpuTimeMsPerNode" getter cfg
    , get @"certSizeBytesConstant" getter cfg
    , get @"certSizeBytesPerNode" getter cfg
    ]

instance ToJSON Config where
  toJSON :: Config -> Value
  toJSON = configToJSONWith always

  toEncoding :: Config -> Encoding
  toEncoding = configToEncodingWith always

newtype OmitDefault a = OmitDefault a
  deriving newtype (Show, Generic)

instance ToJSON (OmitDefault Config) where
  toJSON :: OmitDefault Config -> Value
  toJSON (OmitDefault cfg) = configToJSONWith omitDefault cfg

  toEncoding :: OmitDefault Config -> Encoding
  toEncoding (OmitDefault cfg) = configToEncodingWith omitDefault cfg

instance FromJSON Config where
  parseJSON = withObject "Config" $ \obj -> do
    relayStrategy <- parseFieldOrDefault @Config @"relayStrategy" obj
    tcpCongestionControl <- parseFieldOrDefault @Config @"tcpCongestionControl" obj
    multiplexMiniProtocols <- parseFieldOrDefault @Config @"multiplexMiniProtocols" obj
    treatBlocksAsFull <- parseFieldOrDefault @Config @"treatBlocksAsFull" obj
    leiosStageLengthSlots <- parseFieldOrDefault @Config @"leiosStageLengthSlots" obj
    leiosStageActiveVotingSlots <- parseFieldOrDefault @Config @"leiosStageActiveVotingSlots" obj
    leiosVoteSendRecvStages <- parseFieldOrDefault @Config @"leiosVoteSendRecvStages" obj
    txGenerationDistribution <- parseFieldOrDefault @Config @"txGenerationDistribution" obj
    txSizeBytesDistribution <- parseFieldOrDefault @Config @"txSizeBytesDistribution" obj
    txValidationCpuTimeMs <- parseFieldOrDefault @Config @"txValidationCpuTimeMs" obj
    txMaxSizeBytes <- parseFieldOrDefault @Config @"txMaxSizeBytes" obj
    rbGenerationProbability <- parseFieldOrDefault @Config @"rbGenerationProbability" obj
    rbGenerationCpuTimeMs <- parseFieldOrDefault @Config @"rbGenerationCpuTimeMs" obj
    rbHeadValidationCpuTimeMs <- parseFieldOrDefault @Config @"rbHeadValidationCpuTimeMs" obj
    rbHeadSizeBytes <- parseFieldOrDefault @Config @"rbHeadSizeBytes" obj
    rbBodyMaxSizeBytes <- parseFieldOrDefault @Config @"rbBodyMaxSizeBytes" obj
    rbBodyLegacyPraosPayloadValidationCpuTimeMsConstant <- parseFieldOrDefault @Config @"rbBodyLegacyPraosPayloadValidationCpuTimeMsConstant" obj
    rbBodyLegacyPraosPayloadValidationCpuTimeMsPerByte <- parseFieldOrDefault @Config @"rbBodyLegacyPraosPayloadValidationCpuTimeMsPerByte" obj
    rbBodyLegacyPraosPayloadAvgSizeBytes <- parseFieldOrDefault @Config @"rbBodyLegacyPraosPayloadAvgSizeBytes" obj
    ibGenerationProbability <- parseFieldOrDefault @Config @"ibGenerationProbability" obj
    ibGenerationCpuTimeMs <- parseFieldOrDefault @Config @"ibGenerationCpuTimeMs" obj
    ibHeadSizeBytes <- parseFieldOrDefault @Config @"ibHeadSizeBytes" obj
    ibHeadValidationCpuTimeMs <- parseFieldOrDefault @Config @"ibHeadValidationCpuTimeMs" obj
    ibBodyValidationCpuTimeMsConstant <- parseFieldOrDefault @Config @"ibBodyValidationCpuTimeMsConstant" obj
    ibBodyValidationCpuTimeMsPerByte <- parseFieldOrDefault @Config @"ibBodyValidationCpuTimeMsPerByte" obj
    ibBodyMaxSizeBytes <- parseFieldOrDefault @Config @"ibBodyMaxSizeBytes" obj
    ibBodyAvgSizeBytes <- parseFieldOrDefault @Config @"ibBodyAvgSizeBytes" obj
    ibDiffusionStrategy <- parseFieldOrDefault @Config @"ibDiffusionStrategy" obj
    ibDiffusionMaxWindowSize <- parseFieldOrDefault @Config @"ibDiffusionMaxWindowSize" obj
    ibDiffusionMaxHeadersToRequest <- parseFieldOrDefault @Config @"ibDiffusionMaxHeadersToRequest" obj
    ibDiffusionMaxBodiesToRequest <- parseFieldOrDefault @Config @"ibDiffusionMaxBodiesToRequest" obj
    ebGenerationProbability <- parseFieldOrDefault @Config @"ebGenerationProbability" obj
    ebGenerationCpuTimeMs <- parseFieldOrDefault @Config @"ebGenerationCpuTimeMs" obj
    ebValidationCpuTimeMs <- parseFieldOrDefault @Config @"ebValidationCpuTimeMs" obj
    ebSizeBytesConstant <- parseFieldOrDefault @Config @"ebSizeBytesConstant" obj
    ebSizeBytesPerIb <- parseFieldOrDefault @Config @"ebSizeBytesPerIb" obj
    ebDiffusionStrategy <- parseFieldOrDefault @Config @"ebDiffusionStrategy" obj
    ebDiffusionMaxWindowSize <- parseFieldOrDefault @Config @"ebDiffusionMaxWindowSize" obj
    ebDiffusionMaxHeadersToRequest <- parseFieldOrDefault @Config @"ebDiffusionMaxHeadersToRequest" obj
    ebDiffusionMaxBodiesToRequest <- parseFieldOrDefault @Config @"ebDiffusionMaxBodiesToRequest" obj
    voteGenerationProbability <- parseFieldOrDefault @Config @"voteGenerationProbability" obj
    voteGenerationCpuTimeMsConstant <- parseFieldOrDefault @Config @"voteGenerationCpuTimeMsConstant" obj
    voteGenerationCpuTimeMsPerIb <- parseFieldOrDefault @Config @"voteGenerationCpuTimeMsPerIb" obj
    voteValidationCpuTimeMs <- parseFieldOrDefault @Config @"voteValidationCpuTimeMs" obj
    voteThreshold <- parseFieldOrDefault @Config @"voteThreshold" obj
    voteBundleSizeBytesConstant <- parseFieldOrDefault @Config @"voteBundleSizeBytesConstant" obj
    voteBundleSizeBytesPerEb <- parseFieldOrDefault @Config @"voteBundleSizeBytesPerEb" obj
    voteDiffusionStrategy <- parseFieldOrDefault @Config @"voteDiffusionStrategy" obj
    voteDiffusionMaxWindowSize <- parseFieldOrDefault @Config @"voteDiffusionMaxWindowSize" obj
    voteDiffusionMaxHeadersToRequest <- parseFieldOrDefault @Config @"voteDiffusionMaxHeadersToRequest" obj
    voteDiffusionMaxBodiesToRequest <- parseFieldOrDefault @Config @"voteDiffusionMaxBodiesToRequest" obj
    certGenerationCpuTimeMsConstant <- parseFieldOrDefault @Config @"certGenerationCpuTimeMsConstant" obj
    certGenerationCpuTimeMsPerNode <- parseFieldOrDefault @Config @"certGenerationCpuTimeMsPerNode" obj
    certValidationCpuTimeMsConstant <- parseFieldOrDefault @Config @"certValidationCpuTimeMsConstant" obj
    certValidationCpuTimeMsPerNode <- parseFieldOrDefault @Config @"certValidationCpuTimeMsPerNode" obj
    certSizeBytesConstant <- parseFieldOrDefault @Config @"certSizeBytesConstant" obj
    certSizeBytesPerNode <- parseFieldOrDefault @Config @"certSizeBytesPerNode" obj
    pure Config{..}

distributionToKVs :: KeyValue e kv => Distribution -> [kv]
distributionToKVs Normal{..} =
  [ "distribution" .= ("normal" :: Text)
  , "mean" .= mean
  , "std_dev" .= std_dev
  ]
distributionToKVs Exp{..} =
  [ "distribution" .= ("exp" :: Text)
  , "lambda" .= lambda
  , "scale" .= scale
  ]
distributionToKVs LogNormal{..} =
  [ "distribution" .= ("log-normal" :: Text)
  , "mu" .= mu
  , "sigma" .= sigma
  ]

instance ToJSON Distribution where
  toJSON :: Distribution -> Value
  toJSON = object . distributionToKVs

  toEncoding :: Distribution -> Encoding
  toEncoding = pairs . mconcat . distributionToKVs

instance FromJSON Distribution where
  parseJSON :: Value -> Parser Distribution
  parseJSON = withObject "Distribution" $ \o -> do
    (distribution :: Text) <- o .: "distribution"
    if
      | distribution == "normal" -> do
          mean <- o .: "mean"
          std_dev <- o .: "std_dev"
          pure Normal{..}
      | distribution == "exp" -> do
          lambda <- o .: "lambda"
          scale <- o .: "scale"
          pure Exp{..}
      | distribution == "log-normal" -> do
          mu <- o .: "mu"
          sigma <- o .: "sigma"
          pure LogNormal{..}
      | otherwise -> do
          typeMismatch "Distribution" (Object o)

defaultEnumOptions :: Options
defaultEnumOptions =
  defaultOptions
    { constructorTagModifier = camelToKebab
    , allNullaryToStringTag = True
    }

instance FromJSON DiffusionStrategy where
  parseJSON = genericParseJSON defaultEnumOptions

instance ToJSON DiffusionStrategy where
  toJSON = genericToJSON defaultEnumOptions
  toEncoding = genericToEncoding defaultEnumOptions

instance FromJSON RelayStrategy where
  parseJSON = genericParseJSON defaultEnumOptions

instance ToJSON RelayStrategy where
  toJSON = genericToJSON defaultEnumOptions
  toEncoding = genericToEncoding defaultEnumOptions

-- | Create a 'Config' from a file.
readConfigEither :: FilePath -> IO (Either ParseException Config)
readConfigEither = Yaml.decodeFileEither

readConfig :: FilePath -> IO Config
readConfig file = do
  e <- readConfigEither file
  case e of
    Left parseError -> do
      hPutStrLn stderr $ displayException parseError
      exitFailure
    Right config -> return config

-- | Write a 'Config' to a file.
writeConfig :: FilePath -> Config -> IO ()
writeConfig = Yaml.encodeFile
