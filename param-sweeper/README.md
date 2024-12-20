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
python run_sweep.py
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

### Output Structure

Results are organized in the `results` directory:

- `configs/config_XXXX.toml` - Configuration files for each run
- `plots/` - Generated plots and visualizations
  - `combined_diffusion.png` - Combined visualization of all message types'
    diffusion
  - Individual analyzer plots and visualizations

## Example Analyzers

Currently implemented analyzers:

- `DiffusionAnalyzer` - Base analyzer for message diffusion through the network
  - `IBDiffusionAnalyzer` - Analysis of input block diffusion
  - `EBDiffusionAnalyzer` - Analysis of execution block diffusion
  - `RBDiffusionAnalyzer` - Analysis of ranking block (Praos) diffusion
  - `VoteDiffusionAnalyzer` - Analysis of vote diffusion
- `StakeConnectivityAnalyzer` - Analysis of stake distribution and network
  connectivity patterns

### Adding Custom Analyzers

1. Create a new analyzer in `src/analyzers/`:

```python
from src.core import SimulationAnalyzer
from typing import Dict, Any

class MyCustomAnalyzer(SimulationAnalyzer):
    def analyze(self, result: SimulationResult) -> Dict[str, Any]:
        """Process simulation events and return metrics dictionary"""
        metrics = {}
        # Process simulation data
        return metrics
    
    def visualize(self, results: SweepResults) -> None:
        """Generate analysis visualizations"""
        # Create plots, save metrics
        pass
```

2. Register your analyzer in `run_sweep.py`:

```python
from src.analyzers.my_custom import MyCustomAnalyzer

sweeper = LeiosParamSweeper(...)
sweeper.register_analyzer(MyCustomAnalyzer())
```

## Contributing
