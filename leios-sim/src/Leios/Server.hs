{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Leios.Server where

import Control.Concurrent.Class.MonadSTM (MonadSTM (modifyTVar), TVar, atomically, newBroadcastTChanIO, writeTChan)
import Control.Concurrent.Class.MonadSTM.TChan (TChan, dupTChan, readTChan)
import Control.Concurrent.Class.MonadSTM.TQueue
import Control.Monad (forever)
import Control.Monad.Class.MonadAsync (race_)
import Control.Monad.IO.Class (liftIO)
import Data.Aeson (Value, encode)
import Data.Text.Lazy.Encoding (decodeUtf8)

import qualified Network.Wai as Wai
import qualified Network.Wai.Handler.Warp as Warp
import qualified Network.Wai.Handler.WebSockets as WS
import Network.Wai.Middleware.RequestLogger (logStdoutDev)
import qualified Network.WebSockets as WS
import qualified Web.Scotty as Sc

-- FIXME: import explicitly
import Leios.Model (Parameters (..), BitsPerSecond (..))

runServer :: TVar IO Parameters -> TQueue IO Value -> IO ()
runServer params queue = do
  let port = 8080
  let settings = Warp.setPort port Warp.defaultSettings
  sapp <- scottyApp params
  clientChannel <- newBroadcastTChanIO
  feedClient queue clientChannel
    `race_` Warp.runSettings
      settings
      (WS.websocketsOr WS.defaultConnectionOptions (wsapp clientChannel) sapp)

feedClient :: MonadSTM m => TQueue m Value -> TChan m Value -> m ()
feedClient input output = forever $ do
  atomically $ do
    readTQueue input >>= writeTChan output

scottyApp :: TVar IO Parameters -> IO Wai.Application
scottyApp params =
  Sc.scottyApp $ do
    Sc.middleware logStdoutDev

    Sc.get "/" $
      Sc.redirect "/index.html"

    Sc.get "/index.html" $
      Sc.file "index.html"

    Sc.get "/index.js" $
      Sc.file "index.js"

    Sc.get "/leios.css" $
      Sc.file "leios.css"

    Sc.post "/api/node-bandwidth" $ do
      bps <- Sc.jsonData
      liftIO $
        atomically $
          modifyTVar params (\p -> p{nodeBandwidth = BitsPerSecond bps})

    Sc.post "/api/lambda" $ do
      λ <- Sc.jsonData
      liftIO $
        atomically $
          modifyTVar params (\p -> p{λ})

wsapp :: TChan IO Value -> WS.ServerApp
wsapp queue pending = do
  conn <- WS.acceptRequest pending
  WS.withPingThread conn 30 (pure ()) $ do
    clientQueue <- atomically $ dupTChan queue
    forever $ do
      msg <- atomically $ readTChan clientQueue
      WS.sendTextData conn $ decodeUtf8 $ encode msg
