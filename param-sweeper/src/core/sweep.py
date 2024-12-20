import logging
from pathlib import Path
from typing import Dict, List, Any, Optional, Iterator
import itertools
import toml

from .types import SimulationConfig, SimulationResult, SweepResults
from .runner import SimulationRunner
from .analyzer import SimulationAnalyzer
from .summary import SweepSummary

logger = logging.getLogger(__name__)

class LeiosParamSweeper:
    """Main class for running parameter sweeps of Leios simulations"""
    
    def __init__(self, 
                 base_config_path: Path,
                 output_dir: Path,
                 param_ranges_path: Optional[Path] = None,
                 clean: bool = True):
        """Initialize parameter sweeper
        
        Args:
            base_config_path: Path to base simulation config
            output_dir: Directory for output files
            param_ranges_path: Optional path to parameter ranges config
            clean: Whether to clean output directory before running
        """
        self.base_config_path = Path(base_config_path)
        self.output_dir = Path(output_dir)
        
        # Clean previous results if requested
        if clean and self.output_dir.exists():
            import shutil
            shutil.rmtree(self.output_dir)
        
        self.output_dir.mkdir(parents=True, exist_ok=True)
        
        # Load configurations
        self.base_config = self._load_toml(base_config_path)
        self.param_ranges = self._load_param_ranges(param_ranges_path)
        
        # Initialize components
        self.analyzers: List[SimulationAnalyzer] = []
        self.runner = SimulationRunner(self.base_config_path)
        self.summary = SweepSummary(self.base_config_path, self.param_ranges)
        
        # Create subdirectories
        self.config_dir = self.output_dir / "configs"
        self.sim_dir = self.output_dir / "simulations"
        self.plot_dir = self.output_dir / "plots"
        
        # Create all directories
        for directory in [self.config_dir, self.sim_dir, self.plot_dir]:
            directory.mkdir(parents=True, exist_ok=True)
    
    def register_analyzer(self, analyzer: SimulationAnalyzer) -> None:
        """Register an analyzer for processing simulation results"""
        self.analyzers.append(analyzer)
    
    def run_sweep(self) -> SweepResults:
        """Run parameter sweep and return results"""
        configs = list(self._generate_configs())
        results = []
        
        # Show sweep overview
        self._print_sweep_overview(configs)
        print()
        
        # Run simulations sequentially
        for i, config in enumerate(configs):
            print(f"\nSimulation {i}:")
            print("="*50)
            
            try:
                result = self.runner.run(config)
                
                # Run analyzers
                for analyzer in self.analyzers:
                    metrics = analyzer.analyze(result)
                    result.metrics.update(metrics)
                
                results.append(result)
            except Exception as e:
                logger.error(f"Failed to run simulation {config.iteration}")
                logger.error(f"Error: {str(e)}")
                results.append(SimulationResult(
                    config=config,
                    metrics={},
                    success=False,
                    error=str(e)
                ))
        
        # Create results
        sweep_results = SweepResults(
            configs=configs,
            results=results,
            output_dir=self.output_dir
        )
        
        # Let each analyzer generate its visualizations
        for analyzer in self.analyzers:
            if hasattr(analyzer, 'visualize'):
                analyzer.visualize(sweep_results)
        
        # Write summary after all visualizations are generated
        self.summary.write_summary(sweep_results)
        
        return sweep_results
    
    def _load_toml(self, path: Path) -> Dict[str, Any]:
        """Load TOML file"""
        with open(path) as f:
            return toml.load(f)
    
    def _load_param_ranges(self, path: Optional[Path]) -> Dict[str, List[Any]]:
        """Load parameter ranges from config or base config"""
        if path:
            ranges = self._load_toml(path)
        else:
            ranges = self._extract_ranges_from_base()
        
        # Validate topology is specified
        if 'topology' not in ranges:
            raise ValueError("No topology specified in parameter ranges")
        
        # Ensure topology exists and is a list
        topology = ranges['topology']
        if not isinstance(topology, list):
            topology = [topology]
        ranges['topology'] = topology
        
        topology_file = topology[0]
        topology_path = self.base_config_path.parent / topology_file
        
        if not topology_path.exists():
            raise FileNotFoundError(f"Topology file not found: {topology_path}")
        
        # Ensure all values are lists
        for key, value in ranges.items():
            if not isinstance(value, list):
                ranges[key] = [value]
        
        return ranges
    
    def _extract_ranges_from_base(self) -> Dict[str, List[Any]]:
        """Extract sweepable parameters from config"""
        non_sweepable = {'nodes', 'links', 'trace_nodes'}
        
        param_ranges = {}
        for key, value in self.base_config.items():
            if key in non_sweepable:
                continue
            
            if isinstance(value, list):
                param_ranges[key] = value
            else:
                param_ranges[key] = [value]
        
        return param_ranges
    
    def _generate_configs(self) -> Iterator[SimulationConfig]:
        """Generate all parameter combinations"""
        param_names = list(self.param_ranges.keys())
        param_values = [self.param_ranges[name] for name in param_names]
        
        for i, values in enumerate(itertools.product(*param_values)):
            params = dict(zip(param_names, values))
            
            # Debug log the params
            logger.debug(f"Generated params for simulation {i}:")
            for key, value in params.items():
                logger.debug(f"  {key}: {value}")
            
            config = SimulationConfig(
                params=params,
                iteration=i,
                output_dir=self.output_dir,
                config_dir=self.config_dir,
                sim_dir=self.sim_dir,
                base_config_path=self.base_config_path
            )
            
            yield config
    
    def _print_sweep_overview(self, configs: List[SimulationConfig]) -> None:
        """Print overview of parameter sweep"""
        print("\n🔄 Parameter Sweep Overview")
        print("="*50)
        print(f"Total simulations: {len(configs)}")
        
        # Show swept parameters
        varying_params = {k: v for k, v in self.param_ranges.items() if len(v) > 1}
        if varying_params:
            print("\n📊 Parameters being swept:")
            for param, values in varying_params.items():
                print(f"  {param}: {', '.join(map(str, values))}")