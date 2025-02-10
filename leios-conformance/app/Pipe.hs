{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TupleSections #-}

import Control.Concurrent.Class.MonadSTM (
  MonadSTM (atomically, modifyTVar'),
 )
import Control.Monad (void, when)
import Control.Monad.IO.Class (MonadIO (..))
import Control.Tracer (Tracer, nullTracer)
import Data.Aeson qualified as A
import Data.ByteString.Char8 qualified as BS8
import Data.ByteString.Lazy qualified as LBS
import Data.ByteString.Lazy.Char8 qualified as LBS8
import Data.Default (def)
import Data.Map qualified as Map (fromList)
import Data.Set qualified as Set (fromList)
import Data.Version (showVersion)
import Options.Applicative qualified as O
import Paths_leios_conformance (version)

import Data.List ((\\))
import Data.Maybe (fromMaybe)
import Leios.Conformance.Model
import Leios.Conformance.Test
import Leios.Conformance.Test.External
import System.Exit (die)
import System.IO
import Prelude hiding (getLine, round)

main :: IO ()
main =
  do
    Command{..} <- O.execParser commandParser
    let hReader = stdin
        hWriter = stdout
    hSetBuffering hReader LineBuffering
    hSetBuffering hWriter LineBuffering
    let
      go node =
        do
          -- Verified that this reads UTF-8.
          (A.eitherDecode . LBS.fromStrict <$> BS8.hGetLine hReader)
            >>= \case
              Right req -> do
                (res, node') <- handle node req
                when verbose $ do
                  LBS8.hPutStrLn stderr $ A.encode req
                  LBS8.hPutStrLn stderr $ A.encode res
                  LBS8.hPutStrLn stderr mempty
                case res of
                  Stopped -> pure ()
                  Failed e -> die e
                  _ -> do
                    -- Verified that this writes UTF-8.
                    LBS8.hPutStrLn hWriter $ A.encode res
                    go node'
              Left e -> die $ show e
     in
      go =<< pure initialModelState

handle :: MonadIO m => MonadSTM m => NodeModel -> NodeRequest -> m (NodeResponse, NodeModel)
handle node =
  \case
    Initialize -> pure (def, node)
    NewSlot ibs ebs votes ->
      let node' = fromMaybe node (makeStep node)
          ibs' = iBs node' \\ ibs
          ebs' = eBs node' \\ ebs
          votes' = vs node' \\ votes
          res = NodeResponse{diffuseIBs = ibs', diffuseEBs = ebs', diffuseVotes = votes'}
       in pure (res, node')
    Stop -> pure (Stopped, node)

newtype Command = Command
  { verbose :: Bool
  }
  deriving (Eq, Ord, Read, Show)

commandParser :: O.ParserInfo Command
commandParser =
  let commandOptions =
        Command
          <$> O.flag False True (O.long "verbose" <> O.help "Whether to output requests, traces, and responses.")
   in O.info
        ( O.helper
            <*> O.infoOption ("leios-simulation-pipe " <> showVersion version) (O.long "version" <> O.help "Show version.")
            <*> commandOptions
        )
        ( O.fullDesc
            <> O.progDesc "This command-line tool simulates a Leios node, reading JSON input and writing JSON output."
            <> O.header "leios-simulation-pipe: simulate a Leios node via pipes"
        )
