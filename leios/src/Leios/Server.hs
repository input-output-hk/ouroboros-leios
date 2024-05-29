{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Leios.Server where

import Control.Concurrent.Class.MonadSTM (atomically)
import Control.Concurrent.Class.MonadSTM.TQueue
import Control.Monad (forever)
import Data.Aeson (Value, encode)
import Data.Text.Lazy.Encoding (decodeUtf8)
import qualified Network.Wai as Wai
import qualified Network.Wai.Handler.Warp as Warp
import qualified Network.Wai.Handler.WebSockets as WS
import Network.Wai.Middleware.RequestLogger (logStdoutDev)
import qualified Network.WebSockets as WS
import qualified Web.Scotty as Sc

runServer :: TQueue IO Value -> IO ()
runServer queue = do
  let port = 8080
  let settings = Warp.setPort port Warp.defaultSettings
  sapp <- scottyApp
  Warp.runSettings settings $ WS.websocketsOr WS.defaultConnectionOptions (wsapp queue) sapp

scottyApp :: IO Wai.Application
scottyApp =
  Sc.scottyApp $ do
    Sc.middleware logStdoutDev

    Sc.get "/" $
      Sc.file "index.html"

wsapp :: TQueue IO Value -> WS.ServerApp
wsapp queue pending = do
  conn <- WS.acceptRequest pending
  WS.withPingThread conn 30 (pure ()) $ do
    forever $ do
      msg <- atomically $ readTQueue queue
      WS.sendTextData conn $ decodeUtf8 $ encode msg
