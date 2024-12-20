from pathlib import Path
from typing import Dict, Any, List
from datetime import datetime
import toml
import numpy as np
import os

from .types import SweepResults

class SweepSummary:
    """Generates markdown summaries of parameter sweeps"""
    
    def __init__(self, base_config_path: Path, param_ranges: Dict[str, List[Any]]):
        self.base_config_path = Path(base_config_path)
        self.param_ranges = param_ranges
    
    def write_summary(self, results: SweepResults) -> None:
        """Write summary markdown and print directory overview"""
        self._write_markdown(results)
        self._print_directory_overview(results)
    
    def _write_markdown(self, results: SweepResults) -> None:
        """Write summary markdown to results directory"""
        summary_path = results.output_dir / "summary.md"
        
        with open(summary_path, 'w') as f:
            # Write header
            f.write("# Parameter Sweep Summary\n\n")
            
            # Write topology information
            f.write("## Network\n\n")
            topology_file = self.param_ranges.get('topology', [None])[0]
            if topology_file:
                topology_path = self.base_config_path.parent / topology_file
                if topology_path.exists():
                    # Create relative path from results dir to topology file
                    relative_topology_path = os.path.relpath(
                        topology_path, 
                        results.output_dir
                    )
                    
                    topology = self._load_toml(topology_path)
                    nodes = topology.get('nodes', [])
                    
                    # Count nodes based on stake
                    producer_count = sum(1 for n in nodes if float(n.get('stake', 0)) > 0)
                    relay_count = sum(1 for n in nodes if float(n.get('stake', 0)) == 0)
                    
                    # Calculate stake metrics
                    stakes = [float(n.get('stake', 0)) for n in nodes]
                    total_stake_lovelace = sum(stakes)
                    total_stake_ada = total_stake_lovelace / 1_000_000
                    
                    # Calculate stake distribution metrics
                    stakes_no_zero = [s for s in stakes if s > 0]
                    if stakes_no_zero:
                        min_stake = min(stakes_no_zero) / 1_000_000
                        max_stake = max(stakes_no_zero) / 1_000_000
                        avg_stake = np.mean(stakes_no_zero) / 1_000_000
                        median_stake = np.median(stakes_no_zero) / 1_000_000
                        
                        # Calculate stake concentration (Gini coefficient)
                        stakes_sorted = sorted(stakes_no_zero)
                        n = len(stakes_sorted)
                        gini = sum((2 * i - n - 1) * s for i, s in enumerate(stakes_sorted)) / (n * sum(stakes_sorted))
                    
                    f.write("| Property | Value |\n")
                    f.write("|----------|-------|\n")
                    f.write(f"| Topology File | [`{topology_file}`]({relative_topology_path}) |\n")
                    f.write(f"| Total Nodes | {len(nodes)} |\n")
                    f.write(f"| Producer Nodes | {producer_count} (with stake) |\n")
                    f.write(f"| Relay Nodes | {relay_count} (no stake) |\n")
                    f.write(f"| Total Stake | {total_stake_ada:,.0f} ADA |\n")
                    
                    if stakes_no_zero:
                        f.write("\n### Stake Distribution\n\n")
                        f.write("| Metric | Value |\n")
                        f.write("|--------|-------|\n")
                        f.write(f"| Minimum Stake | {min_stake:,.0f} ADA |\n")
                        f.write(f"| Maximum Stake | {max_stake:,.0f} ADA |\n")
                        f.write(f"| Average Stake | {avg_stake:,.0f} ADA |\n")
                        f.write(f"| Median Stake | {median_stake:,.0f} ADA |\n")
                        f.write(f"| Gini Coefficient | {gini:.3f} |\n")
                else:
                    f.write(f"Topology file `{topology_file}` not found\n")
            f.write("\n")
            
            # Write all parameters in one table
            f.write("## Parameters\n\n")
            f.write("| Parameter | Value |\n")
            f.write("|-----------|-------|\n")
            
            # Write swept parameters first
            varying_params = {k: v for k, v in self.param_ranges.items() if len(v) > 1}
            for param, values in varying_params.items():
                f.write(f"| {param} | {', '.join(map(str, values))} |\n")
            
            # Write fixed parameters
            fixed_params = {k: v[0] for k, v in self.param_ranges.items() 
                          if len(v) == 1 and k != 'topology'}
            for param, value in sorted(fixed_params.items()):
                f.write(f"| {param} | {value} |\n")
            f.write("\n")
            
            # Write simulation details with relative links
            f.write("## Simulation Details\n\n")
            f.write("| Simulation | Status | Config | Output | Parameters |\n")
            f.write("|------------|---------|---------|---------|------------|\n")
            for result in results.results:
                # Build parameters string
                param_str = ""
                if varying_params:
                    params = []
                    for param in varying_params:
                        value = result.config.params[param]
                        if isinstance(value, list):
                            value = value[0]
                        params.append(f"{param}: {value}")
                    param_str = "<br>".join(params)
                
                # Create relative paths for links
                config_rel = Path("configs") / result.config.config_file.name
                output_rel = Path("simulations") / result.config.output_file.name
                
                status = "✅ Success" if result.success else "❌ Failed"
                
                row = [
                    str(result.config.iteration),
                    status,
                    f"[`{result.config.config_file.name}`]({config_rel})",
                    f"[`{result.config.output_file.name}`]({output_rel})",
                    param_str
                ]
                f.write(f"| {' | '.join(row)} |\n")
                
                # Write error on next row if failed
                if not result.success:
                    f.write(f"| | | | | Error: {result.error} |\n")
            
            # Write timestamp
            f.write(f"\n*Generated on {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}*\n")
    
    def _print_directory_overview(self, results: SweepResults) -> None:
        """Print overview of generated files"""
        print("\n📁 Generated Files Overview")
        print("="*50)
        
        base_dir = results.output_dir
        print(f"\n📂 {base_dir}")
        
        # Print summary
        summary_file = base_dir / "summary.md"
        if summary_file.exists():
            size = self._format_size(summary_file.stat().st_size)
            print(f"├── 📝 summary.md ({size})")
        
        # Print configs
        config_dir = base_dir / "configs"
        if config_dir.exists() and list(config_dir.glob("*.toml")):
            print("├── 🔧 configs/")
            config_files = sorted(config_dir.glob("*.toml"))
            for i, f in enumerate(config_files):
                prefix = "├──" if i < len(config_files) - 1 else "└──"
                size = self._format_size(f.stat().st_size)
                print(f"│   {prefix} {f.name} ({size})")
        
        # Print simulation logs
        sim_dir = base_dir / "simulations"
        if sim_dir.exists() and list(sim_dir.glob("*.jsonl")):
            print("├── 📈 simulations/")
            sim_files = sorted(sim_dir.glob("*.jsonl"))
            for i, f in enumerate(sim_files):
                prefix = "├──" if i < len(sim_files) - 1 else "└──"
                size = self._format_size(f.stat().st_size)
                print(f"│   {prefix} {f.name} ({size})")
        
        # Print plots
        plot_dir = base_dir / "plots"
        if plot_dir.exists():
            plot_files = sorted(plot_dir.glob("*.png"))
            if plot_files:
                print("└── 📊 plots/")
                for i, f in enumerate(plot_files):
                    prefix = "├──" if i < len(plot_files) - 1 else "└──"
                    size = self._format_size(f.stat().st_size)
                    print(f"    {prefix} {f.name} ({size})")
            else:
                print("└── (no plot files generated)")
        else:
            print("└── (no plot files generated)")
        
        print()  # Add final spacing
    
    def _format_size(self, size: int) -> str:
        """Format file size in human readable format"""
        for unit in ['B', 'KB', 'MB', 'GB']:
            if size < 1024:
                return f"{size:.1f} {unit}"
            size /= 1024
        return f"{size:.1f} TB"
    
    def _load_toml(self, path: Path) -> Dict[str, Any]:
        """Load TOML file"""
        with open(path) as f:
            return toml.load(f) 
    
    def _get_editor_url_scheme(self) -> str:
        """Get the appropriate URL scheme for the current editor"""
        import os
        
        # Check if running in Cursor
        if os.environ.get('CURSOR_TERMINAL'):
            return 'cursor://file'
        # Default to VS Code
        return 'vscode://file'