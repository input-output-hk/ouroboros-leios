#!/usr/bin/env python3
import sys
from pathlib import Path
import toml
import logging
import traceback

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
from src.analyzers import StakeConnectivityAnalyzer
from src.analyzers.base_diffusion import BaseDiffusionAnalyzer
from src.analyzers.diffusion_analyzers import IBDiffusionAnalyzer, EBDiffusionAnalyzer, RBDiffusionAnalyzer, VoteDiffusionAnalyzer
from src.analyzers.processing_analyzers import IBProcessingAnalyzer, EBProcessingAnalyzer, RBProcessingAnalyzer, VoteProcessingAnalyzer

def main():
    try:
        # Setup paths relative to script location
        sim_dir = project_root.parent / "sim-rs"
        test_data_dir = sim_dir / "test_data"
        
        # Load param ranges first to get topology
        param_ranges_path = project_root / "sweep_ranges.toml"
        param_ranges = toml.load(param_ranges_path)
        
        topology_file = param_ranges.get('topology')
        
        if not topology_file:
            raise ValueError("No topology specified in sweep_ranges.toml")
            
        # Use the topology file as the base config
        base_config = test_data_dir / topology_file
        
        # Verify topology file exists
        if not base_config.exists():
            raise FileNotFoundError(f"Topology file not found: {base_config}")
        
        # Initialize sweeper with correct base config
        sweeper = LeiosParamSweeper(
            base_config_path=base_config,
            output_dir=project_root / "results",
            param_ranges_path=project_root / "sweep_ranges.toml"
        )
        
        # Create output directory
        sweeper.output_dir.mkdir(parents=True, exist_ok=True)
        
        # Create analyzers
        ib_analyzer = IBDiffusionAnalyzer()
        eb_analyzer = EBDiffusionAnalyzer()
        rb_analyzer = RBDiffusionAnalyzer()
        vote_analyzer = VoteDiffusionAnalyzer()

        ib_processing_analyzer = IBProcessingAnalyzer()
        eb_processing_analyzer = EBProcessingAnalyzer()
        rb_processing_analyzer = RBProcessingAnalyzer()
        vote_processing_analyzer = VoteProcessingAnalyzer()
        
        # Register analyzers
        sweeper.register_analyzer(StakeConnectivityAnalyzer())
        sweeper.register_analyzer(ib_analyzer)
        sweeper.register_analyzer(eb_analyzer)
        sweeper.register_analyzer(rb_analyzer)
        sweeper.register_analyzer(vote_analyzer)

        sweeper.register_analyzer(ib_processing_analyzer)
        sweeper.register_analyzer(eb_processing_analyzer)
        sweeper.register_analyzer(rb_processing_analyzer)
        sweeper.register_analyzer(vote_processing_analyzer)
        
        # Run sweep
        results = sweeper.run_sweep()
        
    except ValueError as e:
        print(f"\n❌ Error: {e}")
        traceback.print_exc()
        sys.exit(1)
    except FileNotFoundError as e:
        print(f"\n❌ Error: {e}")
        traceback.print_exc()
        sys.exit(1)
    except Exception as e:
        print(f"\n❌ Unexpected error: {e}")
        traceback.print_exc()
        sys.exit(1)

if __name__ == "__main__":
    main() 