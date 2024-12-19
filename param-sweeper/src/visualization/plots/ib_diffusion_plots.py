import matplotlib.pyplot as plt
import numpy as np
from pathlib import Path
from typing import Dict, Any, List
import logging

from ...core.types import SweepResults

logger = logging.getLogger(__name__)

class IBDiffusionPlot:
    """Generates plots showing Input Block diffusion patterns"""
    
    def generate(self, results: SweepResults, output_dir: Path) -> None:
        """Generate IB diffusion visualization showing stake fraction reached over time"""
        plt.figure(figsize=(12, 8))
        
        # Define colors for different stage lengths
        colors = plt.cm.Set2(np.linspace(0, 1, len(results.successful_results())))
        
        has_data = False
        for i, result in enumerate(results.successful_results()):
            metrics = result.metrics
            if not metrics or 'diffusion_times' not in metrics:
                continue
                
            times = metrics['diffusion_times']
            coverage = [c/100.0 for c in metrics['coverage_percentages']]
            
            if not times or not coverage:
                continue
                
            # Sort by time for proper curve
            time_coverage = sorted(zip(times, coverage))
            times, coverage = zip(*time_coverage)
            
            # Get stage length for label
            stage_length = metrics.get('stage_length', 0)
            
            # Plot with consistent color
            color = colors[i]
            plt.plot(times, coverage, 'o', alpha=0.3, color=color, label=f'Stage Length: {stage_length}s')
            
            # Fit polynomial curve
            z = np.polyfit(times, coverage, 3)
            p = np.poly1d(z)
            
            # Generate smooth curve
            x = np.linspace(min(times), max(times), 100)
            plt.plot(x, p(x), '-', alpha=0.8, color=color)
            
            has_data = True
        
        if not has_data:
            return
            
        plt.xlabel('Time (seconds)')
        plt.ylabel('Network Coverage')
        plt.title('Input Block Diffusion Progress')
        plt.grid(True, alpha=0.3)
        plt.legend()
        
        # Save plot in plots directory
        plot_path = output_dir / "plots" / "ib_diffusion.png"
        plt.savefig(plot_path, bbox_inches='tight')
        plt.close()