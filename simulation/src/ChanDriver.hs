{-# LANGUAGE GADTs #-}

module ChanDriver where

import Chan
import Network.TypedProtocol

data ProtocolMessage ps where
  ProtocolMessage :: SomeMessage st -> ProtocolMessage ps

chanDriver :: Chan m (ProtocolMessage ps) -> Driver ps pr () m
chanDriver _ch = undefined
