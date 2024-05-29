{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Leios.Server where

import Control.Concurrent.Class.MonadSTM (MonadSTM, atomically, newBroadcastTChanIO, writeTChan)
import Control.Concurrent.Class.MonadSTM.TChan (TChan, dupTChan, readTChan)
import Control.Concurrent.Class.MonadSTM.TQueue
import Control.Monad (forever)
import Control.Monad.Class.MonadAsync (race_)
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
  clientChannel <- newBroadcastTChanIO
  feedClient queue clientChannel
    `race_` Warp.runSettings
      settings
      (WS.websocketsOr WS.defaultConnectionOptions (wsapp clientChannel) sapp)

feedClient :: MonadSTM m => TQueue m Value -> TChan m Value -> m ()
feedClient input output = forever $ do
  atomically $ do
    readTQueue input >>= writeTChan output

scottyApp :: IO Wai.Application
scottyApp =
  Sc.scottyApp $ do
    Sc.middleware logStdoutDev

    Sc.get "/" $
      Sc.redirect "/index.html"

    Sc.get "/index.html" $
      Sc.file "index.html"

    Sc.get "/index.js" $
      Sc.file "index.js"

wsapp :: TChan IO Value -> WS.ServerApp
wsapp queue pending = do
  conn <- WS.acceptRequest pending
  WS.withPingThread conn 30 (pure ()) $ do
    clientQueue <- atomically $ dupTChan queue
    forever $ do
      msg <- atomically $ readTChan clientQueue
      WS.sendTextData conn $ decodeUtf8 $ encode msg
