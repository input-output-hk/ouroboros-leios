# Simulation Parameter Sweeper Tool

A Python-based tool for running parameter sweep experiments on the Leios Rust
simulation (soon Haskell too).

## Setup

### Prerequisites

- Python 3.8 or higher
- pip (Python package installer)
- Rust toolchain (for running simulations)

### Installation

1. Create and activate a virtual environment:

```bash
# Create virtual environment
python -m venv sweeper

# Activate virtual environment
# On Windows:
sweeper\Scripts\activate
# On macOS/Linux:
source sweeper/bin/activate
```

2. Install required packages:

```bash
pip install -r requirements.txt
```

## Usage

### Running Parameter Sweeps

1. Configure your parameter ranges in `sweep_ranges.toml`:

```toml
# Base simulation parameters
topology = "simple.toml"  # References an existing topology file
slots = [50, 100]        # Will run simulations with both 50 and 100 slots

# Example parameter ranges
block_generation_probability = [0.05, 0.1]  # Will test both values
ib_generation_probability = [5.0]           # Single value, won't be swept
```

2. Run the sweeper:

```bash
python sweep.py
```

### Parameter Sweep Configuration

The `sweep_ranges.toml` file defines which parameters to sweep:

- Single values in lists (e.g., `[5.0]`) are kept constant
- Multiple values (e.g., `[0.05, 0.1]`) create separate simulations for each
  value
- The sweeper generates all combinations of multi-value parameters
- Example: If you have:
  ```toml
  slots = [50, 100]
  block_generation_probability = [0.05, 0.1]
  ```
  This will run 4 simulations (2 × 2 combinations)

### Adding Custom Analyzers

1. Create a new analyzer in `analyzers/`:

```python
from .base import SimulationAnalyzer
from .events import Event, EventType
import matplotlib.pyplot as plt
from typing import Dict, List

class MyCustomAnalyzer(SimulationAnalyzer):
    name = "my_custom"  # Used for metric prefixes and plot filenames
    
    def process_events(self, events: List[Event]) -> Dict[str, float]:
        """Process events and return metrics"""
        metrics = {}
        for event in events:
            if event.is_type(EventType.SLOT):
                # Process event...
                pass
        return metrics
    
    def generate_plots(self, results_df, output_dir):
        """Generate visualization plots"""
        plt.figure(figsize=(10, 6))
        # Create plots...
        plt.savefig(output_dir / "plots" / f"{self.name}_plot.png")
        plt.close()
```

2. Register your analyzer in `sweep.py`:

```python
from analyzers.my_custom import MyCustomAnalyzer

sweeper = LeiosParamSweeper(...)
sweeper.register_analyzer(MyCustomAnalyzer())
```

### Available Event Types

The following events can be analyzed:

- `SLOT` - New slot started
- `TRANSACTION_GENERATED` - New transaction created
- `TRANSACTION_SENT/RECEIVED` - Transaction network events
- `INPUT_BLOCK_GENERATED` - New input block created
- `ENDORSER_BLOCK_GENERATED` - New endorser block created
- And more... (see `analyzers/events.py`)

### Output Structure

Results are saved in the `results` directory:

- `config_*.toml` - Configuration files for each simulation
- `sim_*.jsonl` - Simulation event logs
- `plots/` - Generated analysis plots grouped by analyzer

## Example Analyzers

Currently implemented analyzers:

- `TopologyAnalyzer` - Network topology analysis and visualization
  ([see example analyses](tests/topology/README.md))

### Example Topology Configurations

The `tests/topology/` directory contains several example network configurations:

- `small` - A compact 25-node network with realistic stake distribution and
  connectivity patterns, ideal for quick testing and development
- `medium` - A moderate-sized network with balanced stake distribution and
  typical relay/producer node relationships
- `realistic` - A large-scale network configuration modeling real-world stake
  distribution and network topology
- `thousand` - A high-scale test configuration with 1000+ nodes, useful for
  performance and scalability testing

Each topology directory contains:

- `config_0000.toml` - The network configuration file
- `topology_metrics.png` - Visualization of network metrics and connectivity
- `ib_diffusion.png` - Analysis of input block propagation patterns
- `topology_issues.md` - Detailed report of network characteristics and
  potential issues

## Contributing

To add new analysis capabilities:

1. Create a new analyzer class inheriting from `SimulationAnalyzer`
2. Implement the required methods:
   - `process_events()` - Calculate metrics from events
   - `generate_plots()` - Create visualizations
3. Register your analyzer with the sweeper
