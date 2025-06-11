{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE TupleSections #-}

module Leios.Tracing.Util (
  Minimum (..),
  Maximum (..),
) where

import Data.Aeson (FromJSON (..))

newtype Minimum a = Minimum {getMinimum :: Maybe a}

instance Show a => Show (Minimum a) where
  show (Minimum Nothing) = "NA"
  show (Minimum (Just x)) = show x

instance Eq a => Eq (Minimum a) where
  Minimum (Just x) == Minimum (Just y) = x == y
  Minimum Nothing == Minimum Nothing = True
  _ == _ = False

instance Ord a => Ord (Minimum a) where
  Minimum (Just x) `compare` Minimum (Just y) = x `compare` y
  Minimum (Just _) `compare` Minimum Nothing = LT
  Minimum Nothing `compare` Minimum (Just _) = GT
  Minimum Nothing `compare` Minimum Nothing = EQ

instance Functor Minimum where
  fmap f = Minimum . fmap f . getMinimum

instance Ord a => Semigroup (Minimum a) where
  x <> y = if x < y then x else y

instance Ord a => Monoid (Minimum a) where
  mempty = Minimum Nothing

instance FromJSON a => FromJSON (Minimum a) where
  parseJSON = fmap Minimum . parseJSON

newtype Maximum a = Maximum {getMaximum :: Maybe a}

instance Show a => Show (Maximum a) where
  show (Maximum Nothing) = "NA"
  show (Maximum (Just x)) = show x

instance Eq a => Eq (Maximum a) where
  Maximum (Just x) == Maximum (Just y) = x == y
  Maximum Nothing == Maximum Nothing = True
  _ == _ = False

instance Ord a => Ord (Maximum a) where
  Maximum (Just x) `compare` Maximum (Just y) = x `compare` y
  Maximum (Just _) `compare` Maximum Nothing = LT
  Maximum Nothing `compare` Maximum (Just _) = GT
  Maximum Nothing `compare` Maximum Nothing = EQ

instance Functor Maximum where
  fmap f = Maximum . fmap f . getMaximum

instance Ord a => Semigroup (Maximum a) where
  x <> y = if x > y then x else y

instance Ord a => Monoid (Maximum a) where
  mempty = Maximum Nothing

instance FromJSON a => FromJSON (Maximum a) where
  parseJSON = fmap Maximum . parseJSON
