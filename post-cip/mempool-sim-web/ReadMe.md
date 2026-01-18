# Mempool Simulation

Discrete-event simulation of Cardano mempool propagation with adversarial front-running.

Simulates how transactions propagate through a network of nodes, where some nodes are adversaries that front-run honest transactions by replacing them with their own versions.

## Setup

```bash
nix develop  # or install Node.js 18+
npm install
```

## Usage

```bash
npm run cli -- [options]
```

### Options

```
-n, --nodes <number>         Number of honest nodes (default: 50)
-d, --degree <number>        Node connectivity degree (default: 6)
-a, --adversaries <number>   Number of adversary nodes (default: 2)
--adversary-degree <number>  Adversary connectivity (default: 18)
-t, --tx-count <number>      Transactions to inject (default: 250)
-l, --latency <seconds>      Network latency (default: 0.1)
-w, --bandwidth <bps>        Bandwidth in bytes/sec (default: 1250000)
```

### Examples

Basic run with defaults:
```bash
npm run cli
```

Small network test:
```bash
npm run cli -- -n 20 -a 1 --adversary-degree 6 -t 50
```

Larger simulation:
```bash
npm run cli -- -n 100 -a 5 -t 500
```

High adversary connectivity:
```bash
npm run cli -- -n 50 -a 3 --adversary-degree 30 -t 200
```

## How it works

1. Generates a random regular graph of honest nodes
2. Adds adversary nodes with configurable connectivity
3. Injects transactions at random honest nodes
4. Transactions propagate via offer/request/send protocol
5. Adversary nodes front-run honest txs by creating adversarial versions
6. Reports final mempool contents (honest vs adversarial tx counts)

## Output

The simulation logs:
- Network configuration
- Topology (node connections)
- Per-node mempool state (at debug level)
- Final statistics: honest vs adversarial transaction fractions
