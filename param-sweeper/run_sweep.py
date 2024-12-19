#!/usr/bin/env python3
import sys
from pathlib import Path

# Add project root to Python path
project_root = Path(__file__).parent
sys.path.insert(0, str(project_root))

from src.core import LeiosParamSweeper
from src.analyzers.ib_diffusion import IBDiffusionAnalyzer

def main():
    # Setup paths relative to script location
    sim_dir = project_root.parent / "sim-rs"
    
    # Initialize sweeper
    sweeper = LeiosParamSweeper(
        base_config_path=sim_dir / "test_data/small.toml",
        output_dir=project_root / "results",
        param_ranges_path=project_root / "sweep_ranges.toml"
    )
    
    # Create output directory
    sweeper.output_dir.mkdir(parents=True, exist_ok=True)
    
    # Register analyzer(s)
    analyzer = IBDiffusionAnalyzer()
    sweeper.register_analyzer(analyzer)
    
    # Run sweep - visualization is now handled by analyzer
    results = sweeper.run_sweep()
    
if __name__ == "__main__":
    main() 