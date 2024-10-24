This repository contains simulation and visualisation code to help with
the design and validation of Ouroboros Leios.

The simulations are not completely configurable from the command line.
The code for the simulation configurations needs to be adjusted or
extended to be able to run different experiments.

The current simulation covers a few examples:

* Basic TCP examples
* A simple block relaying protocol
* A Leios-like traffic pattern for input blocks over a global-scale p2p network

The tool supports two visulaisation output styles:

* A live visualisation using a Gtk+ window
* Output of animation frames to .png files, to turn into a video

For creating videos use a command like
```
ffmpeg -i example/frame-%d.png -vf format=yuv420p example.mp4
```

The `ouroboros-net-vis` command line is
```
Vizualisations of Ouroboros-related network simulations

Usage: ouroboros-net-vis VIZNAME [--frames-dir DIR] [--seconds SEC] 
                         [--skip-seconds SEC] [--cpu-render] 
                         [--720p | --1080p | --resolution (W,H)]

  Either show a visualisation in a window, or output animation frames to a
  directory.

Available options:
  -h,--help                Show this help text
  --frames-dir DIR         Output animation frames to directory
  --seconds SEC            Output N seconds of animation
  --skip-seconds SEC       Skip the first N seconds of animation
  --cpu-render             Use CPU-based client side Cairo rendering
  --720p                   Use 720p resolution
  --1080p                  Use 1080p resolution
  --resolution (W,H)       Use a specific resolution
```
The current `VISNAME` examples are:

* tcp-1: a simple example of TCP slow start behaviour
* tcp-2: comparing different bandwidths
* tcp-3: comparing different traffic patterns
* relay-1: a single pair of nodes using the relaying protocol
* relay-2: four nodes using the relaying protocol
* p2p-1: a Leios-like traffic pattern simulation of input blocks
* p2p-2: a variation with more nodes in the p2p graph
