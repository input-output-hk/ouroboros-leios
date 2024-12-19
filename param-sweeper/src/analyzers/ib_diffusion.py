from typing import Dict, Any
import json
import numpy as np
import logging
import matplotlib.pyplot as plt

from ..core.types import SimulationResult
from ..core.analyzer import SimulationAnalyzer
from ..core.sweep import SweepResults

logger = logging.getLogger(__name__)

class IBDiffusionAnalyzer(SimulationAnalyzer):
    """Analyzes Input Block diffusion through the network"""
    
    name = "ib_diffusion"
    
    def analyze(self, result: SimulationResult) -> Dict[str, Any]:
        """Analyze IB diffusion from simulation output"""
        if not result.success:
            logger.warning("Skipping failed simulation")
            return {}
            
        metrics = {
            "total_ibs": 0,
            "diffusion_times": [],
            "coverage_percentages": [],
            "stage_length": result.config.params.get("stage_length", 0)
        }
        
        try:
            # First pass - collect all nodes that receive IBs
            active_nodes = set()
            with open(result.config.output_file) as f:
                for line in f:
                    try:
                        event = json.loads(line)
                        msg = event.get("message", {})
                        msg_type = msg.get("type")
                        
                        if msg_type == "InputBlockReceived":
                            recipient = msg.get("recipient")
                            if recipient:
                                active_nodes.add(recipient)
                    except json.JSONDecodeError:
                        continue
            
            total_nodes = len(active_nodes)
            logger.debug(f"Found {total_nodes} active nodes")
            
            if total_nodes == 0:
                logger.warning("No active nodes found in simulation")
                return metrics
            
            # Track IB generation and reception
            ib_data = {}
            
            # Second pass - track IB diffusion
            with open(result.config.output_file) as f:
                for line in f:
                    try:
                        event = json.loads(line)
                        msg = event.get("message", {})
                        slot_time = event.get("time", 0)
                        msg_type = msg.get("type")
                        
                        if msg_type == "InputBlockGenerated":
                            ib_id = msg.get("id")
                            if ib_id is not None:
                                ib_data[ib_id] = {
                                    "generated_time": slot_time,
                                    "receptions": set()
                                }
                                logger.debug(f"Found IB generation: {ib_id}")
                        
                        elif msg_type == "InputBlockReceived":
                            ib_id = msg.get("id")
                            recipient = msg.get("recipient")
                            if ib_id in ib_data:
                                ib_data[ib_id]["receptions"].add((recipient, slot_time))
                                logger.debug(f"Found IB reception: {ib_id} -> {recipient}")
                    except json.JSONDecodeError:
                        continue
            
            logger.debug(f"Found {len(ib_data)} IBs")
            
            # Calculate metrics
            for ib_id, data in ib_data.items():
                if data["receptions"]:
                    receptions = sorted(data["receptions"], key=lambda x: x[1])
                    for i, (_, slot_time) in enumerate(receptions, 1):
                        coverage_pct = (i / total_nodes) * 100
                        diffusion_time = (slot_time - data["generated_time"]) * metrics["stage_length"]
                        metrics["diffusion_times"].append(diffusion_time)
                        metrics["coverage_percentages"].append(coverage_pct)
            
            metrics["total_ibs"] = len(ib_data)
            logger.debug(f"Generated {len(metrics['diffusion_times'])} data points")
            
            return metrics
            
        except Exception as e:
            logger.error(f"Error analyzing simulation: {e}", exc_info=True)
            return metrics
    
    def visualize(self, results: SweepResults) -> None:
        """Generate IB diffusion visualization"""
        if not results.successful_results():
            return
            
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
        plot_path = results.output_dir / "plots" / "ib_diffusion.png"
        plt.savefig(plot_path, bbox_inches='tight')
        plt.close()