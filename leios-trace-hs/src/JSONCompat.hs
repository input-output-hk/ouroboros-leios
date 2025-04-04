{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}

module JSONCompat where

import Data.Aeson.Key (fromString)
import Data.Aeson.Types (FromJSON (..), KeyValue ((.=)), Object, Parser, ToJSON (..), explicitParseFieldMaybe, parserCatchError, (.!=), (.:))
import Data.Char (isUpper, toLower, toUpper)
import Data.Default (Default (..))
import Debug.Trace
import GHC.Records (HasField (..))
import GHC.TypeLits (KnownSymbol (..), SSymbol, fromSSymbol)

kebabToCamel :: String -> String
kebabToCamel = go False
 where
  go _ [] = []
  go _ ('-' : cs) = go True cs
  go b (c : cs) = (if b then toUpper c else c) : go False cs

camelToKebab :: String -> String
camelToKebab = go . lowerFirst
 where
  lowerFirst [] = []
  lowerFirst (c : cs) = toLower c : cs
  go (c : cs)
    | isUpper c = '-' : toLower c : go cs
    | otherwise = c : go cs
  go [] = []

newtype Getter r = Getter {unGetter :: forall f v e kv. SSymbol f -> (HasField f r v, KeyValue e kv, ToJSON v, Eq v) => r -> Maybe kv}

get :: forall fld obj e kv a. (KnownSymbol fld, HasField fld obj a, KeyValue e kv, ToJSON a, Eq a) => Getter obj -> obj -> Maybe kv
get (Getter getter) = getter (symbolSing @fld)

always :: Getter r
always = Getter $ \(fld :: SSymbol fld) obj ->
  let key = fromString (camelToKebab (fromSSymbol fld))
      val = getField @fld obj
   in Just (key .= val)

omitDefault :: Default r => Getter r
omitDefault = Getter $ \(fld :: SSymbol fld) obj ->
  let key = fromString (camelToKebab (fromSSymbol fld))
      getFld = getField @fld
      val = getFld obj
   in if val == getFld def then Nothing else Just (key .= val)

parseFieldOrDefault :: forall obj fld a. (HasField fld obj a, Default obj, KnownSymbol fld, FromJSON a) => Object -> Parser a
parseFieldOrDefault obj =
  explicitParseFieldMaybe tracingParser obj (fromString (camelToKebab (fromSSymbol (symbolSing @fld))))
    .!= defVal
 where
  defVal = getField @fld (def :: obj)
  tracingParser v =
    parseJSON v
      `parserCatchError` ( \path msg ->
                            trace ("Using default value for: " ++ show path ++ " , error: " ++ msg) (pure defVal)
                         )

parseField :: forall obj fld a. (HasField fld obj a, KnownSymbol fld, FromJSON a) => Object -> Parser a
parseField obj = obj .: fromString (camelToKebab (fromSSymbol (symbolSing @fld)))
