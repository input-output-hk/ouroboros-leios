{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Leios.Server where

import Control.Concurrent.Class.MonadSTM.TQueue
import Control.Monad (forever)
import Control.Monad.Class.MonadTimer (threadDelay)
import Data.Aeson (Value)
import Data.Text (Text)
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
  Warp.runSettings settings $ WS.websocketsOr WS.defaultConnectionOptions wsapp sapp

scottyApp :: IO Wai.Application
scottyApp =
  Sc.scottyApp $ do
    Sc.middleware logStdoutDev

    Sc.get "/" $
      Sc.file "index.html"

wsapp :: WS.ServerApp
wsapp pending = do
  conn <- WS.acceptRequest pending
  WS.withPingThread conn 30 (pure ()) $ do
    (msg :: Text) <- WS.receiveData conn
    WS.sendTextData conn $ ("initial> " :: Text) <> msg

    forever $ do
      WS.sendTextData conn $ ("loop data" :: Text)
      threadDelay $ 1 * 1000000
