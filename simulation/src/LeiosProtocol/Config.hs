{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeApplications #-}

module LeiosProtocol.Config where

import Data.Aeson.Encoding (pairs)
import Data.Aeson.Types (Encoding, FromJSON (..), KeyValue ((.=)), Parser, ToJSON (..), Value (..), object, typeMismatch, withObject, (.:))
import Data.Default (Default (..))
import Data.Maybe (catMaybes)
import Data.Text (Text)
import GHC.Generics (Generic)
import JSONCompat (Getter, always, get, omitDefault, parseFieldOrDefault)

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

data Config = Config
  { leiosStageLengthSlots :: Word
  , leiosStageActiveVotingSlots :: Word
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
  , ebGenerationProbability :: Double
  , ebGenerationCpuTimeMs :: DurationMs
  , ebValidationCpuTimeMs :: DurationMs
  , ebSizeBytesConstant :: SizeBytes
  , ebSizeBytesPerIb :: SizeBytes
  , voteGenerationProbability :: Double
  , voteGenerationCpuTimeMsConstant :: DurationMs
  , voteGenerationCpuTimeMsPerIb :: DurationMs
  , voteValidationCpuTimeMs :: DurationMs
  , voteThreshold :: Word
  , voteOneEbPerVrfWin :: Bool
  , voteSizeBytesConstant :: SizeBytes
  , voteSizeBytesPerNode :: SizeBytes
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
      { leiosStageLengthSlots = 20
      , leiosStageActiveVotingSlots = 1
      , txGenerationDistribution = Exp{lambda = 0.85, scale = Just 1000}
      , txSizeBytesDistribution = LogNormal{mu = 6.833, sigma = 1.127}
      , txValidationCpuTimeMs = 1.5
      , txMaxSizeBytes = 16384
      , rbGenerationProbability = 5.0e-2
      , rbGenerationCpuTimeMs = 300.0
      , rbHeadValidationCpuTimeMs = 1.0
      , rbHeadSizeBytes = 32
      , rbBodyMaxSizeBytes = 90112
      , rbBodyLegacyPraosPayloadValidationCpuTimeMsConstant = 50.0
      , rbBodyLegacyPraosPayloadValidationCpuTimeMsPerByte = 0.0005
      , rbBodyLegacyPraosPayloadAvgSizeBytes = 0
      , ibGenerationProbability = 0.5
      , ibGenerationCpuTimeMs = 300.0
      , ibHeadSizeBytes = 32
      , ibHeadValidationCpuTimeMs = 1.0
      , ibBodyValidationCpuTimeMsConstant = 50.0
      , ibBodyValidationCpuTimeMsPerByte = 0.0005
      , ibBodyMaxSizeBytes = 327680
      , ibBodyAvgSizeBytes = 327680
      , ebGenerationProbability = 5.0
      , ebGenerationCpuTimeMs = 300.0
      , ebValidationCpuTimeMs = 1.0
      , ebSizeBytesConstant = 32
      , ebSizeBytesPerIb = 32
      , voteGenerationProbability = 500.0
      , voteGenerationCpuTimeMsConstant = 1.0
      , voteGenerationCpuTimeMsPerIb = 1.0
      , voteValidationCpuTimeMs = 3.0
      , voteThreshold = 150
      , voteOneEbPerVrfWin = False
      , voteSizeBytesConstant = 32
      , voteSizeBytesPerNode = 32
      , certGenerationCpuTimeMsConstant = 50.0
      , certGenerationCpuTimeMsPerNode = 1.0
      , certValidationCpuTimeMsConstant = 50.0
      , certValidationCpuTimeMsPerNode = 1.0
      , certSizeBytesConstant = 32
      , certSizeBytesPerNode = 32
      }

configToJSONWith :: Getter Config -> Config -> Value
configToJSONWith getter = object . configToKVsWith getter

configToEncodingWith :: Getter Config -> Config -> Encoding
configToEncodingWith getter = pairs . mconcat . configToKVsWith getter

configToKVsWith :: KeyValue e kv => Getter Config -> Config -> [kv]
configToKVsWith getter cfg =
  catMaybes
    [ get @"leiosStageLengthSlots" getter cfg
    , get @"leiosStageActiveVotingSlots" getter cfg
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
    , get @"ebGenerationProbability" getter cfg
    , get @"ebGenerationCpuTimeMs" getter cfg
    , get @"ebValidationCpuTimeMs" getter cfg
    , get @"ebSizeBytesConstant" getter cfg
    , get @"ebSizeBytesPerIb" getter cfg
    , get @"voteGenerationProbability" getter cfg
    , get @"voteGenerationCpuTimeMsConstant" getter cfg
    , get @"voteGenerationCpuTimeMsPerIb" getter cfg
    , get @"voteValidationCpuTimeMs" getter cfg
    , get @"voteThreshold" getter cfg
    , get @"voteOneEbPerVrfWin" getter cfg
    , get @"voteSizeBytesConstant" getter cfg
    , get @"voteSizeBytesPerNode" getter cfg
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
    leiosStageLengthSlots <- parseFieldOrDefault @Config @"leiosStageLengthSlots" obj
    leiosStageActiveVotingSlots <- parseFieldOrDefault @Config @"leiosStageActiveVotingSlots" obj
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
    ebGenerationProbability <- parseFieldOrDefault @Config @"ebGenerationProbability" obj
    ebGenerationCpuTimeMs <- parseFieldOrDefault @Config @"ebGenerationCpuTimeMs" obj
    ebValidationCpuTimeMs <- parseFieldOrDefault @Config @"ebValidationCpuTimeMs" obj
    ebSizeBytesConstant <- parseFieldOrDefault @Config @"ebSizeBytesConstant" obj
    ebSizeBytesPerIb <- parseFieldOrDefault @Config @"ebSizeBytesPerIb" obj
    voteGenerationProbability <- parseFieldOrDefault @Config @"voteGenerationProbability" obj
    voteGenerationCpuTimeMsConstant <- parseFieldOrDefault @Config @"voteGenerationCpuTimeMsConstant" obj
    voteGenerationCpuTimeMsPerIb <- parseFieldOrDefault @Config @"voteGenerationCpuTimeMsPerIb" obj
    voteValidationCpuTimeMs <- parseFieldOrDefault @Config @"voteValidationCpuTimeMs" obj
    voteThreshold <- parseFieldOrDefault @Config @"voteThreshold" obj
    voteOneEbPerVrfWin <- parseFieldOrDefault @Config @"voteOneEbPerVrfWin" obj
    voteSizeBytesConstant <- parseFieldOrDefault @Config @"voteSizeBytesConstant" obj
    voteSizeBytesPerNode <- parseFieldOrDefault @Config @"voteSizeBytesPerNode" obj
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
