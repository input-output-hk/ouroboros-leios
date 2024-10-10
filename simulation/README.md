This repository contains simulation and visualisation code to help with
the design and validation of Ouroboros Leios.

The simulations are not completely configurable from the command line.
The code for the simulation configurations needs to be adjusted or
extended to be able to run different experiments.

The current simulation covers a few examples:

* Basic TCP examples
* A simple block relaying protocol
* A Leios-like traffic pattern for input blocks over a global-scale p2p network

The tool supports two visualisation output styles:

* A live visualisation using a Gtk+ window
* Output of animation frames to .png files, to turn into a video

For creating videos use a command like
```
ffmpeg -i example/frame-%d.png -vf format=yuv420p example.mp4
```

## Running simulator

Assuming the executable has been built in the directory containing this `README`, one can run the simulator with `cabal run ouroboros-net-vis`. Inline help is provided through the usual `--help` or `-h` flags.
