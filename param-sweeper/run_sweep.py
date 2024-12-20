#!/usr/bin/env python3
import sys
from pathlib import Path
import toml
import logging

# Configure logging
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(levelname)s - %(message)s',
    datefmt='%Y-%m-%d %H:%M:%S'
)
logger = logging.getLogger(__name__)

# Add project root to Python path
project_root = Path(__file__).parent
sys.path.insert(0, str(project_root))

from src.core import LeiosParamSweeper
from src.analyzers.ib_diffusion import IBDiffusionAnalyzer

def main():
    try:
        # Setup paths relative to script location
        sim_dir = project_root.parent / "sim-rs"
        test_data_dir = sim_dir / "test_data"
        
        # Load param ranges first to get topology
        param_ranges_path = project_root / "sweep_ranges.toml"
        param_ranges = toml.load(param_ranges_path)
        
        topology_file = param_ranges.get('topology', [None])[0]
        
        if not topology_file:
            raise ValueError("No topology specified in sweep_ranges.toml")
            
        # Use the topology file as the base config
        base_config = test_data_dir / topology_file
        
        # Verify topology file exists
        if not base_config.exists():
            raise FileNotFoundError(f"Topology file not found: {base_config}")
            
        logger.info(f"Using topology file: {base_config}")
        
        # Initialize sweeper with correct base config
        sweeper = LeiosParamSweeper(
            base_config_path=base_config,
            output_dir=project_root / "results",
            param_ranges_path=project_root / "sweep_ranges.toml"
        )
        
        # Create output directory
        sweeper.output_dir.mkdir(parents=True, exist_ok=True)
        
        # Register analyzer(s)
        analyzer = IBDiffusionAnalyzer()
        sweeper.register_analyzer(analyzer)
        
        # Run sweep
        results = sweeper.run_sweep()
        
    except ValueError as e:
        print(f"\n❌ Error: {e}")
        sys.exit(1)
    except FileNotFoundError as e:
        print(f"\n❌ Error: {e}")
        sys.exit(1)
    except Exception as e:
        print(f"\n❌ Unexpected error: {e}")
        sys.exit(1)

if __name__ == "__main__":
    main() 