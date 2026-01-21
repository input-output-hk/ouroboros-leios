# Mempool Simulation

Discrete-event simulation of Cardano mempool propagation with adversarial front-running.

Simulates how transactions propagate through a network of nodes, where some nodes are adversaries that front-run honest transactions by replacing them with their own versions.

## Fidelity to the actual Cardano mempool

The simulation implements a highly idealized representation of the Cardano mempool protocol rules. It aims to build intuition about the operation of the mempool.

1. The network topology is that of a [Regular Random Graph](https://en.wikipedia.org/wiki/Random_regular_graph). *The churn of hot/warm/cold peers is not modeled.*
2. Transactions IDs are announced to upstream peers.
3. Downstream peers download the transaction body from the first upstream peer that announces its ID.
4. Each node's mempool has a finite, fixed size of twice the size of a block.
5. A node will not request transactions that will overfill its mempool.
6. A node applies "backpressure" to clients submitting transaction to it: those transactions wait in a queue until there is room in the mempool.
7. When a block is produced, transactions included in that block are removed from the simulation. *Note that the simulation does not model block propagation or chain selection.*
8. A simple bandwidth plus latency model is used to represent transmission of data.

The adversarial model is similarly idealized. It aims to build intuition regarding front-running or MEV (miner extractable value): the adversarial node replaces each transaction with one to its own advantage. *In real life, of course, only a fraction of transactions (arbitrage opportunties, entries in order books, etc.) might be susceptible to such front running.*

- Each adversarial node connects to a specified number of upstream and downstream nodes. *Honest nodes will not refuse such connections.*
- When an adversarial node receives a transaction, it *does not announce it to its upstream peers*. Instead, it creates a new, conflicting transaction and announces that instead.
- Crafting the front-run transaction takes a finite amount of time in excess of processing an honest transaction.
- Statistics for the fraction of honest vs adversarial transactions in blocks are tallied.

Future enhancement could improve the fidelity, but the above algorithm is likely sufficient for building basic intuitions.

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

```console
$ npm run cli -- --help

Usage: mempool-sim [options]

Memory pool simulation with adversarial front-running

Options:
  -V, --version                output the version number
  -n, --nodes <number>         Number of honest nodes (default: "50")
  -d, --degree <number>        Node connectivity degree (default: "6")
  -b, --block <bytes>          Block size in bytes (default: "90000")
  -l, --latency <seconds>      Network latency in seconds (default: "0.1")
  -w, --bandwidth <bps>        Bandwidth in bytes per second (default: "1250000")
  -a, --adversaries <number>   Number of adversary nodes (default: "2")
  --adversary-degree <number>  Adversary connectivity degree (default: "18")
  --adversary-delay <seconds>  Time needed for adversary to front-run a transaction (default: "0.002")
  -t, --tx-count <number>      Number of transactions to inject (default: "250")
  --tx-duration <seconds>      Duration over which to inject transactions (default: "20")
  --tx-size-min <bytes>        Minimum transaction size (default: "200")
  --tx-size-max <bytes>        Maximum transaction size (default: "16384")
  --slot-duration <seconds>    Block slot duration in seconds (default: "20")
  -s, --slots <number>         Number of slots to simulate (default: "10")
  --log-level <level>          Logging detail (choices: "fatal", "error", "warn", "info", "debug", "trace", default: "info")
  -h, --help                   display help for command
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
