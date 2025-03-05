{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}

module Main where

import Control.Exception (Exception (displayException))
import Control.Monad
import Data.Aeson (eitherDecodeFileStrict')
import Data.Default (Default (..))
import Data.List (find)
import qualified Data.Map as Map
import Data.Maybe (fromMaybe, listToMaybe)
import qualified Data.Yaml as Yaml
import qualified ExamplesRelay
import qualified ExamplesRelayP2P
import qualified ExamplesTCP
import LeiosProtocol.Common (BlockBody, PraosConfig)
import qualified LeiosProtocol.Config as OnDisk
import qualified LeiosProtocol.Short.DataSimP2P as DataShortLeiosP2P
import qualified LeiosProtocol.Short.VizSim as VizShortLeios
import qualified LeiosProtocol.Short.VizSimP2P as VizShortLeiosP2P
import qualified LeiosProtocol.VizSimTestRelay as VizSimTestRelay
import ModelTCP (kilobytes)
import Options.Applicative (
  Alternative ((<|>)),
  HasValue,
  Mod,
  Parser,
  ParserInfo,
  ParserPrefs,
  asum,
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
  short,
  showDefault,
  showDefaultWith,
  showHelpOnEmpty,
  strArgument,
  strOption,
  subparser,
  switch,
  value,
  (<**>),
 )
import Options.Applicative.Types (ReadM)
import qualified PraosProtocol.ExamplesPraosP2P as VizPraosP2P
import qualified PraosProtocol.VizSimBlockFetch as VizBlockFetch
import qualified PraosProtocol.VizSimChainSync as VizChainSync
import qualified PraosProtocol.VizSimPraos as VizPraos
import SimTypes
import System.Exit (exitFailure)
import System.FilePath
import System.IO (hPutStrLn, stderr)
import qualified System.Random as Random
import TimeCompat
import Topology hiding (topologyOptions)
import Viz

main :: IO ()
main = do
  customExecParser parserPrefs parserInfoOptions >>= \case
    VizCommand opt -> runVizCommand opt
    SimCommand opt -> runSimOptions opt
    CliCommand opt -> runCliOptions opt

shownDefValue :: (Show a, HasValue f) => a -> Mod f a
shownDefValue a = value a <> showDefault

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
    , command "generate-topology" . info (CliCommand <$> parserCliGenerateTopology <**> helper) $
        progDesc "Generate a topology from a world shape and expected links. Other parameters are fixed and meant to be edited after the fact."
    , command "report-data" . info (CliCommand <$> parserReportData <**> helper) $
        progDesc "Outputs diffusion data as .csv. Either from simulation output or idealized graph diffusion."
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
  | VizPraosP2P1
      { seed :: Int
      , configOptions :: ConfigOptions
      , topologyOptions :: TopologyOptions
      }
  | VizPraosP2P2
  | VizRelayTest1
  | VizRelayTest2
  | VizRelayTest3
  | VizShortLeios1
  | VizShortLeiosP2P1
      { seed :: Int
      , configOptions :: ConfigOptions
      , topologyOptions :: TopologyOptions
      }

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
    <$> parserSeed
    <*> parserConfigOptions
    <*> parserTopologyOptions

parserSeed :: Parser Int
parserSeed =
  option
    auto
    ( long "seed"
        <> metavar "NUMBER"
        <> help "The seed for the random number generator."
        <> shownDefValue 0
    )

parserShortLeiosP2P1 :: Parser VizSubCommand
parserShortLeiosP2P1 =
  VizShortLeiosP2P1
    <$> option
      auto
      ( long "seed"
          <> metavar "NUMBER"
          <> help "The seed for the random number generator."
          <> shownDefValue 0
      )
    <*> parserConfigOptions
    <*> parserTopologyOptions

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
    p2pNetwork <- execTopologyOptions rng1 topologyOptions
    cfg <- execConfigOptions configOptions
    pure $ VizPraosP2P.example1 rng2 cfg p2pNetwork
  VizPraosP2P2 -> pure VizPraosP2P.example2
  VizRelayTest1 -> pure VizSimTestRelay.example1
  VizRelayTest2 -> pure VizSimTestRelay.example2
  VizRelayTest3 -> pure VizSimTestRelay.example3
  VizShortLeios1 -> pure VizShortLeios.example1
  VizShortLeiosP2P1{..} -> do
    let rng0 = Random.mkStdGen seed
    let (rng1, rng2) = Random.split rng0
    p2pNetwork <- execTopologyOptions rng1 topologyOptions
    cfg <- execConfigOptions configOptions
    pure $ VizShortLeiosP2P.example2 rng2 cfg p2pNetwork

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

data SimOptions = SimOptions
  { simCommand :: SimCommand
  , simOutputSeconds :: Time
  , simOutputFile :: FilePath
  }

runSimOptions :: SimOptions -> IO ()
runSimOptions SimOptions{..} = case simCommand of
  SimPraosDiffusion{..} -> do
    let rng0 = Random.mkStdGen seed
    let (rng1, rng2) = Random.split rng0
    config <- execConfigOptions configOptions
    p2pNetwork <- execTopologyOptions rng1 topologyOptions
    -- let bandwidth = 10 * 125_000_000 :: Bytes -- 10 Gbps TODO: set in config
    VizPraosP2P.example1000Diffusion rng2 config p2pNetwork simOutputSeconds simOutputFile
  SimShortLeios{..} -> do
    let rng0 = Random.mkStdGen seed
    let (rng1, rng2) = Random.split rng0
    config <- execConfigOptions configOptions
    p2pNetwork <- execTopologyOptions rng1 topologyOptions
    let outputCfg =
          DataShortLeiosP2P.SimOutputConfig
            { logFile = listToMaybe [dropExtension simOutputFile <.> "log" | not skipLog]
            , emitControl
            , dataFile = Just simOutputFile
            , analize
            , stop = simOutputSeconds
            , sharedFormat
            }
    DataShortLeiosP2P.exampleSim rng2 config p2pNetwork outputCfg

parserSimOptions :: Parser SimOptions
parserSimOptions =
  SimOptions
    <$> parserSimCommand
    <*> fmap
      (Time . fromIntegral @Int)
      ( option
          auto
          ( long "output-seconds"
              <> metavar "SECONDS"
              <> help "Output N seconds of simulation."
              <> shownDefValue 40
          )
      )
    <*> strOption
      ( long "output-file"
          <> metavar "FILE"
          <> help "Output simulation data to file."
      )

data SimCommand
  = SimPraosDiffusion
      { seed :: Int
      , configOptions :: ConfigOptions
      , topologyOptions :: TopologyOptions
      }
  | SimShortLeios
      { seed :: Int
      , configOptions :: ConfigOptions
      , topologyOptions :: TopologyOptions
      , emitControl :: Bool
      , skipLog :: Bool
      , analize :: Bool
      , sharedFormat :: Bool
      }

parserSimCommand :: Parser SimCommand
parserSimCommand =
  subparser . mconcat $
    [ commandGroup "Available simulations:"
    , command "praos-diffusion" . info (parserSimPraosDiffusion <**> helper) $
        progDesc ""
    , command "short-leios" . info (parserShortLeios <**> helper) $
        progDesc ""
    ]

parserSimPraosDiffusion :: Parser SimCommand
parserSimPraosDiffusion =
  SimPraosDiffusion
    <$> parserSeed
    <*> parserConfigOptions
    <*> parserTopologyOptions

parserShortLeios :: Parser SimCommand
parserShortLeios =
  SimShortLeios
    <$> parserSeed
    <*> parserConfigOptions
    <*> parserTopologyOptions
    <*> switch (long "log-control" <> help "Include control messages in log.")
    <*> switch (long "no-log" <> help "Do not output event log.")
    <*> switch (long "analize" <> help "Calculate metrics and statistics.")
    <*> switch (long "shared-log-format" <> help "Use log format documented in trace.haskell.d.ts")

data ConfigOptions
  = LeiosConfigFile FilePath
  | LeiosConfig OnDisk.Config

execConfigOptions :: ConfigOptions -> IO OnDisk.Config
execConfigOptions = \case
  LeiosConfigFile configFile -> OnDisk.readConfig configFile
  LeiosConfig config -> pure config

execConfigOptionsForPraos :: ConfigOptions -> IO (PraosConfig BlockBody)
execConfigOptionsForPraos = fmap VizPraosP2P.convertConfig . execConfigOptions

parserConfigOptions :: Parser ConfigOptions
parserConfigOptions =
  asum
    [ LeiosConfigFile <$> parserLeiosConfigFile
    , pure $ LeiosConfig def
    ]

parserLeiosConfigFile :: Parser FilePath
parserLeiosConfigFile =
  strOption $
    short 'l'
      <> long "leios-config-file"
      <> metavar "FILE"
      <> help "File containing the configuration values for the Leios simulation."

parserOverrideUnlimited :: Parser Bytes
parserOverrideUnlimited =
  Bytes
    <$> option
      auto
      ( long "override-unlimited-bandwidth"
          <> metavar "BYTESPERSEC"
          <> help "Values to use for link bandwidth instead of unlimited (which is not supported yet)."
          <> shownDefValue (fromBytes $ kilobytes 1000)
      )

--------------------------------------------------------------------------------
-- Utility Commands
--------------------------------------------------------------------------------

data CliCommand
  = CliConvertBenchTopology {inputBenchTopologyFile :: FilePath, inputBenchLatenciesFile :: FilePath, outputTopologyFile :: FilePath}
  | CliLayoutTopology {inputTopologyFile :: FilePath, outputTopologyFile :: FilePath}
  | CliGenerateTopology {seed :: Int, topologyGenerationOptions :: TopologyGenerationOptions, outputTopologyFile :: FilePath}
  | CliReportData {outputDir :: Maybe FilePath, reportConfigFile :: FilePath, printTargetsOnly :: Bool, simDataFile :: FilePath}

runCliOptions :: CliCommand -> IO ()
runCliOptions = \case
  -- Convert from a benchmark topology to the shared topology format
  CliConvertBenchTopology{..} -> do
    topologyCluster <- readTopologyFromBenchTopology inputBenchTopologyFile inputBenchLatenciesFile 1
    writeTopology outputTopologyFile (SomeTopology SCLUSTER topologyCluster)
  -- Convert from a topology with cluster names to a toplogy with coordinates
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
  -- Generate a random topology using the topology characteristics
  CliGenerateTopology{..} -> do
    let rng = Random.mkStdGen seed
    p2pNetwork@P2PNetwork{..} <- execTopologyGenerationOptions rng topologyGenerationOptions
    let totalStake = fromIntegral $ 100 * Map.size p2pNodes
    writeTopology outputTopologyFile $ p2pNetworkToSomeTopology totalStake p2pNetwork
  CliReportData{..} -> do
    let prefixDir = fromMaybe (takeDirectory simDataFile) outputDir
    reportConfig <- Yaml.decodeFileThrow reportConfigFile
    DataShortLeiosP2P.reportLeiosData prefixDir simDataFile reportConfig printTargetsOnly

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

parserCliGenerateTopology :: Parser CliCommand
parserCliGenerateTopology =
  CliGenerateTopology
    <$> parserSeed
    <*> parserTopologyGenerationOptions
    <*> strOption
      ( long "output-topology"
          <> short 'o'
          <> metavar "FILE"
          <> help "The output topology file."
      )

parserReportData :: Parser CliCommand
parserReportData =
  CliReportData
    <$> optional (strOption $ short 'o' <> long "output-dir")
    <*> strOption (short 'c' <> long "report-config")
    <*> switch (long "print-targets-only")
    <*> strArgument (metavar "SIMDATA")

--------------------------------------------------------------------------------
-- Parsing Topography Options
--------------------------------------------------------------------------------

execTopologyOptions :: Random.RandomGen g => g -> TopologyOptions -> IO P2PNetwork
execTopologyOptions rng = \case
  TopologyFile simpleTopologyFile -> do
    -- TODO: infer world size from latencies
    let world = World (1200, 1000) Rectangle
    validateP2PNetwork =<< readP2PTopographyFromSomeTopology defaultParams world simpleTopologyFile
  TopologyGenerationOptions topologyGenerationOptions -> execTopologyGenerationOptions rng topologyGenerationOptions

execTopologyGenerationOptions :: Random.RandomGen g => g -> TopologyGenerationOptions -> IO P2PNetwork
execTopologyGenerationOptions rng =
  validateP2PNetwork <=< \case
    TopologyGenerationStrategyFile topologyGenerationStrategyFile ->
      eitherDecodeFileStrict' topologyGenerationStrategyFile >>= \case
        Right topologyGenerationStrategy -> execTopologyGenerationOptions rng (TopologyGenerationStrategy topologyGenerationStrategy)
        Left errorMessage -> fail $ "Could not decode P2PTopographyCharacteristics from '" <> topologyGenerationStrategyFile <> "':\n" <> errorMessage
    TopologyGenerationStrategy topologyGenerationStrategy -> generateTopology rng topologyGenerationStrategy

data TopologyOptions
  = TopologyFile FilePath
  | TopologyGenerationOptions TopologyGenerationOptions

instance Default TopologyOptions where
  def = TopologyGenerationOptions def

parserTopologyOptions :: Parser TopologyOptions
parserTopologyOptions =
  asum
    [ TopologyFile <$> parserTopologyFile
    , TopologyGenerationOptions <$> parserTopologyGenerationOptions
    , pure def
    ]

parserTopologyFile :: Parser FilePath
parserTopologyFile =
  strOption
    ( short 't'
        <> long "topology-file"
        <> metavar "FILE"
        <> help "A topology file describing the world topology."
    )

data TopologyGenerationOptions
  = TopologyGenerationStrategyFile FilePath
  | TopologyGenerationStrategy TopologyGenerationStrategy

instance Default TopologyGenerationOptions where
  def = TopologyGenerationStrategy def

parserTopologyGenerationOptions :: Parser TopologyGenerationOptions
parserTopologyGenerationOptions =
  (TopologyGenerationStrategyFile <$> parserTopologyGenerationStrategyFile)
    <|> (TopologyGenerationStrategy <$> parserTopologyGenerationStrategy)

parserTopologyGenerationStrategyFile :: Parser FilePath
parserTopologyGenerationStrategyFile =
  strOption
    ( long "tg"
        <> long "topology-generation-strategy-file"
        <> metavar "FILE"
        <> help "A file describing the topology generation strategy."
    )

parserTopologyGenerationStrategy :: Parser TopologyGenerationStrategy
parserTopologyGenerationStrategy =
  subparser . mconcat $
    [ commandGroup "Available topology generation strategies:"
    , command "close-and-random" . info (PickLinksCloseAndRandom <$> parserPickLinksCloseAndRandomOptions <**> helper) $
        progDesc "Pick links to close and random nodes."
    ]

parserPickLinksCloseAndRandomOptions :: Parser PickLinksCloseAndRandomOptions
parserPickLinksCloseAndRandomOptions =
  PickLinksCloseAndRandomOptions
    <$> parserWorld
    <*> option
      auto
      ( long "tg-num-nodes"
          <> metavar "NUMBER"
          <> help "The number of nodes."
          <> shownDefValue (numNodes def)
      )
    <*> option
      auto
      ( long "tg-num-links-close"
          <> metavar "NUMBER"
          <> help "The number of links to close peers for each node."
          <> shownDefValue (numCloseLinksPerNode def)
      )
    <*> option
      auto
      ( long "tg-num-links-random"
          <> metavar "NUMBER"
          <> help "The number of links to random peers for each node."
          <> shownDefValue (numRandomLinksPerNode def)
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
    ( long "tg-world-shape"
        <> metavar "SHAPE"
        <> help "The shape of the generated world. Supported shapes are rectangle and cylinder."
        <> value def
        <> showDefaultWith showWorldShape
    )

readWorldShape :: ReadM WorldShape
readWorldShape = eitherReader $ \txt ->
  case lookup txt worldShapeLabels of
    Just s -> Right s
    Nothing -> Left ("Could not parse WorldShape '" <> txt <> "'")

showWorldShape :: WorldShape -> String
showWorldShape s = case find ((== s) . snd) worldShapeLabels of
  Just (txt, _) -> txt
  Nothing -> "Error: Unknown worldshape '" <> show s <> "'"

worldShapeLabels :: [(String, WorldShape)]
worldShapeLabels = [("rectangle", Rectangle), ("cylinder", Cylinder)]

parserWorldDimensions :: Parser WorldDimensions
parserWorldDimensions =
  (,)
    <$> option
      auto
      ( long "tg-world-width"
          <> metavar "SECONDS"
          <> help "The east-west size of the generated world."
          <> shownDefValue (fst $ worldDimensions def)
      )
    <*> option
      auto
      ( long "tg-world-height"
          <> metavar "SECONDS"
          <> help "The north-south size of the generated world."
          <> shownDefValue (snd $ worldDimensions def)
      )
