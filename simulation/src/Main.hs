{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}

module Main where

import Control.Exception (Exception (displayException))
import Control.Monad
import Data.Aeson (eitherDecodeFileStrict')
import Data.Default (Default (..))
import Data.Maybe (fromMaybe)
import qualified ExamplesRelay
import qualified ExamplesRelayP2P
import qualified ExamplesTCP
import qualified LeiosProtocol.Config as OnDisk
import LeiosProtocol.Short.Node (NumCores (..))
import qualified LeiosProtocol.Short.VizSim as VizShortLeios
import qualified LeiosProtocol.Short.VizSimP2P as VizShortLeiosP2P
import qualified LeiosProtocol.VizSimTestRelay as VizSimTestRelay
import Options.Applicative (
  Alternative ((<|>)),
  Parser,
  ParserInfo,
  ParserPrefs,
  auto,
  command,
  commandGroup,
  customExecParser,
  eitherReader,
  flag',
  help,
  helpShowGlobals,
  helper,
  info,
  long,
  metavar,
  option,
  optional,
  prefs,
  progDesc,
  readerError,
  short,
  showHelpOnEmpty,
  str,
  strOption,
  subparser,
  switch,
  value,
  (<**>),
 )
import Options.Applicative.Types (ReadM)
import P2P (P2PTopography (..), P2PTopographyCharacteristics (..), genArbitraryP2PTopography)
import qualified PraosProtocol.ExamplesPraosP2P as VizPraosP2P
import qualified PraosProtocol.VizSimBlockFetch as VizBlockFetch
import qualified PraosProtocol.VizSimChainSync as VizChainSync
import qualified PraosProtocol.VizSimPraos as VizPraos
import SimTypes (World (..), WorldDimensions, WorldShape (..))
import System.Exit (exitFailure)
import System.IO (hPutStrLn, stderr)
import qualified System.Random as Random
import TimeCompat
import Topology
import Viz

main :: IO ()
main = do
  customExecParser parserPrefs parserInfoOptions >>= \case
    VizCommand opt -> runVizCommand opt
    SimCommand opt -> runSimOptions opt
    CliCommand opt -> runCliOptions opt

parserPrefs :: ParserPrefs
parserPrefs =
  prefs . mconcat $
    [ showHelpOnEmpty
    , helpShowGlobals
    ]

parserInfoOptions :: ParserInfo Options
parserInfoOptions = info (parserOptions <**> helper) mempty

data Options
  = VizCommand VizCommand
  | SimCommand SimOptions
  | CliCommand CliCommand

parserOptions :: Parser Options
parserOptions =
  subparser . mconcat $
    [ command "viz" . info (VizCommand <$> parserVizCommand <**> helper) $
        progDesc "Run a visualisation. See 'ols viz -h' for details."
    , command "sim" . info (SimCommand <$> parserSimOptions <**> helper) $
        progDesc "Run a simulation. See 'ols sim -h' for details."
    , command "convert-bench-topology" . info (CliCommand <$> parserCliConvertBenchTopology <**> helper) $
        progDesc "Convert from a benchmark topology and a latency database to a topology with clusters."
    , command "convert-cluster-topology" . info (CliCommand <$> parserCliLayoutTopology <**> helper) $
        progDesc "Convert from a topology with clusters to a topology with location coordinates."
    ]

--------------------------------------------------------------------------------
-- Visualisation Commands
--------------------------------------------------------------------------------

runVizCommand :: VizCommand -> IO ()
runVizCommand opt@VizCommandWithOptions{..} = do
  viz0 <- vizOptionsToViz opt
  let viz = maybe viz0 ((`slowmoVisualization` viz0) . secondsToDiffTime) vizSlowDown
  case vizOutputFramesDir of
    Nothing ->
      let gtkVizConfig =
            defaultGtkVizConfig
              { gtkVizCpuRendering = vizCpuRendering
              , gtkVizResolution = vizSize
              }
       in vizualise gtkVizConfig viz
    Just outputFramesDir ->
      let animVizConfig =
            defaultAnimVizConfig
              { animVizFrameFiles = \n -> outputFramesDir ++ "/frame-" ++ show n ++ ".png"
              , animVizDuration = fromMaybe 60 vizOutputSeconds
              , animVizStartTime = fromMaybe 0 vizOutputStartTime
              , animVizResolution = vizSize
              }
       in writeAnimationFrames animVizConfig viz

data VizCommand = VizCommandWithOptions
  { vizSubCommand :: VizSubCommand
  , vizOutputFramesDir :: Maybe FilePath
  , vizOutputSeconds :: Maybe Int
  , vizOutputStartTime :: Maybe Int
  , vizCpuRendering :: Bool
  , vizSize :: Maybe VizSize
  , vizSlowDown :: Maybe Double
  }

parserVizCommand :: Parser VizCommand
parserVizCommand =
  VizCommandWithOptions
    <$> parserVizSubCommand
    <*> optional
      ( strOption
          ( long "frames-dir"
              <> metavar "DIR"
              <> help "Output animation frames to directory"
          )
      )
    <*> optional
      ( option
          auto
          ( long "seconds"
              <> metavar "SEC"
              <> help "Output N seconds of animation"
          )
      )
    <*> optional
      ( option
          auto
          ( long "skip-seconds"
              <> metavar "SEC"
              <> help "Skip the first N seconds of animation"
          )
      )
    <*> switch
      ( long "cpu-render"
          <> help "Use CPU-based client side Cairo rendering"
      )
    <*> optional vizSizeOptions
    <*> optional
      ( option
          auto
          ( long "slowdown"
              <> metavar "R"
              <> help "Simulation time speed multiplier, applied on top of predefined speed."
          )
      )
data VizSubCommand
  = VizTCP1
  | VizTCP2
  | VizTCP3
  | VizRelay1
  | VizRelay2
  | VizP2P1
  | VizP2P2
  | VizPCS1
  | VizPBF1
  | VizPraos1
  | VizPraosP2P1 {seed :: Int, blockInterval :: DiffTime, topographyOptions :: TopographyOptions}
  | VizPraosP2P2
  | VizRelayTest1
  | VizRelayTest2
  | VizRelayTest3
  | VizShortLeios1
  | VizShortLeiosP2P1 {seed :: Int, sliceLength :: Int, topographyOptions :: TopographyOptions, numCores :: NumCores}

parserVizSubCommand :: Parser VizSubCommand
parserVizSubCommand =
  subparser . mconcat $
    [ commandGroup "Available visualisations:"
    , command "tcp-1" . info (pure VizTCP1) $
        progDesc ""
    , command "tcp-2" . info (pure VizTCP2) $
        progDesc ""
    , command "tcp-3" . info (pure VizTCP3) $
        progDesc ""
    , command "relay-1" . info (pure VizRelay1) $
        progDesc ""
    , command "relay-2" . info (pure VizRelay2) $
        progDesc ""
    , command "p2p-1" . info (pure VizP2P1) $
        progDesc ""
    , command "p2p-2" . info (pure VizP2P2) $
        progDesc ""
    , command "pcs-1" . info (pure VizPCS1) $
        progDesc
          "A simulation of two nodes running Praos chain-sync."
    , command "pbf-1" . info (pure VizPBF1) $
        progDesc
          "A simulation of two nodes running Praos block-fetch."
    , command "praos-1" . info (pure VizPraos1) $
        progDesc
          "A simulation of two nodes running Praos consensus."
    , command "praos-p2p-1" . info (parserPraosP2P1 <**> helper) $
        progDesc
          "A simulation of 100 nodes running Praos consensus."
    , command "praos-p2p-2" . info (pure VizPraosP2P2) $
        progDesc
          "A simulation of 100 nodes running Praos consensus, \
          \comparing a cylindrical world to a flat world."
    , command "relay-test-1" . info (pure VizRelayTest1) $
        progDesc ""
    , command "relay-test-2" . info (pure VizRelayTest2) $
        progDesc ""
    , command "relay-test-3" . info (pure VizRelayTest3) $
        progDesc ""
    , command "short-leios-1" . info (pure VizShortLeios1) $
        progDesc
          "A simulation of two nodes running Short Leios."
    , command "short-leios-p2p-1" . info (parserShortLeiosP2P1 <**> helper) $
        progDesc
          "A simulation of 100 nodes running Short Leios."
    ]

parserPraosP2P1 :: Parser VizSubCommand
parserPraosP2P1 =
  VizPraosP2P1
    <$> option
      auto
      ( long "seed"
          <> metavar "NUMBER"
          <> help "The seed for the random number generator."
          <> value 0
      )
    <*> option
      (fmap (fromIntegral @Int) auto)
      ( long "block-interval"
          <> metavar "NUMBER"
          <> help "The interval at which blocks are generated."
          <> value 5
      )
    <*> parserTopographyOptions

parserShortLeiosP2P1 :: Parser VizSubCommand
parserShortLeiosP2P1 =
  VizShortLeiosP2P1
    <$> option
      auto
      ( long "seed"
          <> metavar "NUMBER"
          <> help "The seed for the random number generator."
          <> value 0
      )
    <*> option
      (fmap (fromIntegral @Int) auto)
      ( long "slice-length"
          <> metavar "NUMBER"
          <> help "The interval at which ranking blocks are generated."
          <> value 5
      )
    <*> parserTopographyOptions
    <*> option
      readCores
      ( short 'N'
          <> metavar "NUMBER"
          <> value Infinite
          <> help "number of simulated cores for node parallesim, or 'unbounded' (the default)."
      )
 where
  readCores = unbounded <|> finite
   where
    unbounded = do
      s <- str
      if s == "unbounded" then pure Infinite else readerError "unrecognized"
    finite = do
      n <- auto
      if n > 0 then pure (Finite n) else readerError "number of cores should be greater than 0"

vizOptionsToViz :: VizCommand -> IO Visualization
vizOptionsToViz VizCommandWithOptions{..} = case vizSubCommand of
  VizTCP1 -> pure ExamplesTCP.example1
  VizTCP2 -> pure ExamplesTCP.example2
  VizTCP3 -> pure ExamplesTCP.example3
  VizRelay1 -> pure ExamplesRelay.example1
  VizRelay2 -> pure ExamplesRelay.example2
  VizP2P1 -> pure ExamplesRelayP2P.example1
  VizP2P2 -> pure ExamplesRelayP2P.example2
  VizPCS1 -> pure VizChainSync.example1
  VizPBF1 -> pure VizBlockFetch.example1
  VizPraos1 -> pure VizPraos.example1
  VizPraosP2P1{..} -> do
    let rng0 = Random.mkStdGen seed
    let (rng1, rng2) = Random.split rng0
    p2pTopography <- execTopographyOptions rng1 topographyOptions
    pure $ VizPraosP2P.example1 rng2 blockInterval p2pTopography
  VizPraosP2P2 -> pure VizPraosP2P.example2
  VizRelayTest1 -> pure VizSimTestRelay.example1
  VizRelayTest2 -> pure VizSimTestRelay.example2
  VizRelayTest3 -> pure VizSimTestRelay.example3
  VizShortLeios1 -> pure VizShortLeios.example1
  VizShortLeiosP2P1{..} -> do
    let rng0 = Random.mkStdGen seed
    let (rng1, rng2) = Random.split rng0
    p2pTopography <- execTopographyOptions rng1 topographyOptions
    let config =
          def
            { OnDisk.leiosStageLengthSlots = fromIntegral sliceLength
            , OnDisk.rbGenerationProbability = 0.2
            , OnDisk.ibGenerationProbability = 5
            , OnDisk.ebGenerationProbability = 1.5
            , OnDisk.voteGenerationProbability = 500
            , OnDisk.voteThreshold = 150
            }
    pure $ VizShortLeiosP2P.example2 rng2 config p2pTopography numCores

type VizSize = (Int, Int)

vizSizeOptions :: Parser VizSize
vizSizeOptions =
  flag'
    (1280, 720)
    ( long "720p"
        <> help "Use 720p resolution"
    )
    <|> flag'
      (1920, 1080)
      ( long "1080p"
          <> help "Use 1080p resolution"
      )
    <|> option
      auto
      ( long "resolution"
          <> metavar "(W,H)"
          <> help "Use a specific resolution"
      )

--------------------------------------------------------------------------------
-- Simulation Commands
--------------------------------------------------------------------------------

runSimOptions :: SimOptions -> IO ()
runSimOptions SimOptions{..} = case simCommand of
  SimPraosDiffusion10{..} ->
    VizPraosP2P.example1000Diffusion numCloseLinks numRandomLinks simOutputSeconds simOutputFile
  SimPraosDiffusion20{..} ->
    VizPraosP2P.example1000Diffusion numCloseLinks numRandomLinks simOutputSeconds simOutputFile
  SimShortLeios -> do
    -- TODO: read from parameter file
    let numCores = Infinite
    let config =
          def
            { OnDisk.leiosStageLengthSlots = 20
            , OnDisk.rbGenerationProbability = 1 / 20
            , OnDisk.ibGenerationProbability = 5
            , OnDisk.ebGenerationProbability = 1.5
            , OnDisk.voteGenerationProbability = 500
            , OnDisk.voteThreshold = 150
            }
    let seed = 42
    let rng0 = Random.mkStdGen seed
    let (rng1, rng2) = Random.split rng0
    let topographyOptions = TopographyCharacteristics $ P2PTopographyCharacteristics def 100 5 5
    p2pTopography <- execTopographyOptions rng1 topographyOptions
    VizShortLeiosP2P.exampleSim rng2 config p2pTopography numCores simOutputSeconds simOutputFile

data SimOptions = SimOptions
  { simCommand :: SimCommand
  , simOutputSeconds :: Time
  , simOutputFile :: FilePath
  }

parserSimOptions :: Parser SimOptions
parserSimOptions =
  SimOptions
    <$> parserSimCommand
    <*> option
      (Time . fromIntegral @Int <$> auto)
      ( long "output-seconds"
          <> metavar "SECONDS"
          <> help "Output N seconds of simulation."
          <> value (Time $ fromIntegral @Int 40)
      )
    <*> strOption
      ( long "output-file"
          <> metavar "FILE"
          <> help "Output simulation data to file."
      )

data SimCommand
  = SimPraosDiffusion10 {numCloseLinks :: Int, numRandomLinks :: Int}
  | SimPraosDiffusion20 {numCloseLinks :: Int, numRandomLinks :: Int}
  | SimShortLeios

parserSimCommand :: Parser SimCommand
parserSimCommand =
  subparser . mconcat $
    [ commandGroup "Available simulations:"
    , command "praos-diffusion-10" . info parserSimPraosDiffusion10 $
        progDesc ""
    , command "praos-diffusion-20" . info parserSimPraosDiffusion20 $
        progDesc ""
    , command "short-leios" . info parserShortLeios $
        progDesc ""
    ]

parserSimPraosDiffusion10 :: Parser SimCommand
parserSimPraosDiffusion10 =
  SimPraosDiffusion10
    <$> option
      auto
      ( long "num-close-links"
          <> metavar "NUMBER"
          <> help "The number of close-distance links."
          <> value 5
      )
    <*> option
      auto
      ( long "num-random-links"
          <> metavar "NUMBER"
          <> help "The number of random links."
          <> value 5
      )

parserSimPraosDiffusion20 :: Parser SimCommand
parserSimPraosDiffusion20 =
  SimPraosDiffusion20
    <$> option
      auto
      ( long "num-close-links"
          <> metavar "NUMBER"
          <> help "The number of close-distance links."
          <> value 10
      )
    <*> option
      auto
      ( long "num-random-links"
          <> metavar "NUMBER"
          <> help "The number of random links."
          <> value 10
      )

parserShortLeios :: Parser SimCommand
parserShortLeios = pure SimShortLeios

--------------------------------------------------------------------------------
-- Utility Commands
--------------------------------------------------------------------------------

runCliOptions :: CliCommand -> IO ()
runCliOptions = \case
  CliConvertBenchTopology{..} -> do
    topologyCluster <- readTopologyFromBenchTopology inputBenchTopologyFile inputBenchLatenciesFile 1
    writeTopology outputTopologyFile (SomeTopology SCLUSTER topologyCluster)
  CliLayoutTopology{..} -> do
    readTopology inputTopologyFile >>= \case
      Left errMsg -> do
        hPutStrLn stderr (displayException errMsg)
        exitFailure
      Right (SomeTopology SCOORD2D _topology) -> do
        hPutStrLn stderr . concat $ ["Topology already has coordinates: '", inputTopologyFile, "'"]
        exitFailure
      Right (SomeTopology SCLUSTER topologyCluster) -> do
        topologyCoord2D <- layoutTopology defaultParams topologyCluster
        writeTopology outputTopologyFile (SomeTopology SCOORD2D topologyCoord2D)

data CliCommand
  = CliConvertBenchTopology {inputBenchTopologyFile :: FilePath, inputBenchLatenciesFile :: FilePath, outputTopologyFile :: FilePath}
  | CliLayoutTopology {inputTopologyFile :: FilePath, outputTopologyFile :: FilePath}

parserCliConvertBenchTopology :: Parser CliCommand
parserCliConvertBenchTopology =
  CliConvertBenchTopology
    <$> strOption
      ( long "input-bench-topology"
          <> long "ibt"
          <> metavar "FILE"
          <> help "The input topology file."
      )
    <*> strOption
      ( long "input-bench-latencies"
          <> long "ibl"
          <> metavar "FILE"
          <> help "The input latencies database."
      )
    <*> strOption
      ( long "output-topology"
          <> short 'o'
          <> metavar "FILE"
          <> help "The output topology file."
      )

parserCliLayoutTopology :: Parser CliCommand
parserCliLayoutTopology =
  CliLayoutTopology
    <$> strOption
      ( long "input-topology"
          <> short 'i'
          <> metavar "FILE"
          <> help "The input topology file."
      )
    <*> strOption
      ( long "output-latencies"
          <> short 'o'
          <> metavar "FILE"
          <> help "The output topology file."
      )

--------------------------------------------------------------------------------
-- Parsing Topography Options
--------------------------------------------------------------------------------

execTopographyOptions :: Random.RandomGen g => g -> TopographyOptions -> IO P2PTopography
execTopographyOptions rng = checkTopography <=< go
 where
  go = \case
    SimpleTopologyFile simpleTopologyFile -> do
      -- TODO: infer world size from latencies
      let world = World (1200, 1000) Rectangle
      readP2PTopographyFromSomeTopology defaultParams world simpleTopologyFile
    TopographyCharacteristicsFile p2pTopographyCharacteristicsFile -> do
      eitherP2PTopographyCharacteristics <- eitherDecodeFileStrict' p2pTopographyCharacteristicsFile
      case eitherP2PTopographyCharacteristics of
        Right p2pTopographyCharacteristics ->
          pure $ genArbitraryP2PTopography p2pTopographyCharacteristics rng
        Left errorMessage ->
          fail $ "Could not decode P2PTopographyCharacteristics from '" <> p2pTopographyCharacteristicsFile <> "':\n" <> errorMessage
    TopographyCharacteristics p2pTopographyCharacteristics -> do
      pure $ genArbitraryP2PTopography p2pTopographyCharacteristics rng
  checkTopography top@P2PTopography{p2pLinks} = do
    let node_triplets = triangleInequalityCheck p2pLinks
    unless (null node_triplets) $ do
      putStr $
        unlines $
          "Latencies do not respect triangle inequalities for these nodes:" : map show node_triplets
    return top

data TopographyOptions
  = SimpleTopologyFile FilePath
  | TopographyCharacteristicsFile FilePath
  | TopographyCharacteristics P2PTopographyCharacteristics

parserTopographyOptions :: Parser TopographyOptions
parserTopographyOptions =
  parserSimpleTopologyFile
    <|> parserTopographyCharacteristicsFile
    <|> (TopographyCharacteristics <$> parserTopographyCharacteristics)
 where
  parserSimpleTopologyFile =
    SimpleTopologyFile
      <$> strOption
        ( short 't'
            <> long "topology-file"
            <> metavar "FILE"
            <> help "A topology file describing the world topology."
        )
  parserTopographyCharacteristicsFile =
    TopographyCharacteristicsFile
      <$> strOption
        ( long "tc"
            <> long "topology-characteristics-file"
            <> metavar "FILE"
            <> help "A file describing the characteristics of the world topology."
        )

parserTopographyCharacteristics :: Parser P2PTopographyCharacteristics
parserTopographyCharacteristics =
  P2PTopographyCharacteristics
    <$> parserWorld
    <*> option
      auto
      ( long "tc-num-nodes"
          <> metavar "NUMBER"
          <> help "The number of nodes."
          <> value (p2pNumNodes def)
      )
    <*> option
      auto
      ( long "tc-num-links-close"
          <> metavar "NUMBER"
          <> help "The number of links to close peers for each node."
          <> value (p2pNodeLinksClose def)
      )
    <*> option
      auto
      ( long "tc-num-links-random"
          <> metavar "NUMBER"
          <> help "The number of links to random peers for each node."
          <> value (p2pNodeLinksRandom def)
      )

parserWorld :: Parser World
parserWorld =
  World
    <$> parserWorldDimensions
    <*> parserWorldShape

parserWorldShape :: Parser WorldShape
parserWorldShape =
  option
    readWorldShape
    ( long "tc-world-shape"
        <> metavar "SHAPE"
        <> help "The shape of the generated world. Supported shapes are rectangle and cylinder."
        <> value def
    )

readWorldShape :: ReadM WorldShape
readWorldShape = eitherReader $ \txt ->
  if
    | txt == "rectangle" -> Right Rectangle
    | txt == "cylinder" -> Right Cylinder
    | otherwise -> Left ("Could not parse WorldShape '" <> txt <> "'")

parserWorldDimensions :: Parser WorldDimensions
parserWorldDimensions =
  (,)
    <$> option
      auto
      ( long "tc-world-width"
          <> metavar "SECONDS"
          <> help "The east-west size of the generated world."
          <> value (fst $ worldDimensions def)
      )
    <*> option
      auto
      ( long "tc-world-height"
          <> metavar "SECONDS"
          <> help "The north-south length of the generated world."
          <> value (snd $ worldDimensions def)
      )
