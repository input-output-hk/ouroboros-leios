This repository contains simulation and visualisation code to help with
the design and validation of Ouroboros Leios.

The simulations are not completely configurable from the command line.
The code for the simulation configurations needs to be adjusted or
extended to be able to run different experiments.

The current simulation covers a few examples:

- Basic TCP examples
- A simple block relaying protocol
- A Leios-like traffic pattern for input blocks over a global-scale p2p network

The tool supports two visulaisation output styles:

- A live visualisation using a Gtk+ window
- Output of animation frames to .png files, to turn into a video

For creating videos use a command like

```sh
ffmpeg -i example/frame-%d.png -vf format=yuv420p example.mp4
```

The main entry point for the simulation is the `ols` command, which exposes the `viz` subcommand for running visualisations, the `sim` subcommand for running headless simulations, as well as various utility commands.

```
$ cabal run ols -- --help

Usage: ols COMMAND

Available options:
  -h,--help                Show this help text

Available commands:
  viz                      Run a visualisation. See 'ols viz -h' for details.
  sim                      Run a simulation. See 'ols sim -h' for details.
  convert-bench-topology   Convert merge benchmark topology and latency files
                           into a simple topology file.
```

The visualisation subcommand exposes a number of visualisations:

> [!CAUTION]
> The visualisations are under active development, so the following list is almost certainly out of date.
> If you would like an up-to-date list of visualisations, please build and run the command.

```
$ cabal run ols -- viz --help

Usage: ols viz COMMAND [--frames-dir DIR] [--seconds SEC] [--skip-seconds SEC]
               [--cpu-render] [--720p | --1080p | --resolution (W,H)]

  Run a visualisation. See 'ols viz -h' for details.

Available options:
  --frames-dir DIR         Output animation frames to directory
  --seconds SEC            Output N seconds of animation
  --skip-seconds SEC       Skip the first N seconds of animation
  --cpu-render             Use CPU-based client side Cairo rendering
  --720p                   Use 720p resolution
  --1080p                  Use 1080p resolution
  --resolution (W,H)       Use a specific resolution
  -h,--help                Show this help text

Available visualisations:
  tcp-1
  tcp-2
  tcp-3
  relay-1
  relay-2
  p2p-1
  p2p-2
  pcs-1                    A simulation of two nodes running Praos chain-sync.
  pbf-1                    A simulation of two nodes running Praos block-fetch.
  praos-1                  A simulation of two nodes running Praos consensus.
  praos-p2p-1              A simulation of 100 nodes running Praos consensus.
  praos-p2p-2              A simulation of 100 nodes running Praos consensus,
                           comparing a cylindrical world to a flat world.
  relay-test-1
  relay-test-2
  relay-test-3
  short-leios-1            A simulation of two nodes running Short Leios.
  short-leios-p2p-1        A simulation of 100 nodes running Short Leios.
```

Some of these visualisations accept further arguments. For instance:

```
$ cabal run ols -- viz praos-p2p-1 --help

Usage: ols viz praos-p2p-1 [--seed NUMBER] [--block-interval NUMBER]
                           [--topology FILE]

  A simulation of 100 nodes running Praos consensus.

Available options:
  --seed NUMBER            The seed for the random number generator.
  --block-interval NUMBER  The interval at which blocks are generated.
  --topology FILE          The file describing the network topology.
  -h,--help                Show this help text
```

The simulation subcommand exposes a number of simulations:

> [!CAUTION]
> The simulations are under active development, so the following list is almost certainly out of date.
> If you would like an up-to-date list of simulations, please build and run the command.

```
$ cabal run ols -- sim --help

Usage: ols sim COMMAND [--output-seconds SECONDS] --output-file FILE

  Run a simulation. See 'ols sim -h' for details.

Available options:
  --output-seconds SECONDS Output N seconds of simulation.
  --output-file FILE       Output simulation data to file.
  -h,--help                Show this help text

Available simulations:
  praos-diffusion-10
  praos-diffusion-20
```
