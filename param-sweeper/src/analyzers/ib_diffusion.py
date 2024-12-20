from typing import Dict, Any
import json
import numpy as np
import matplotlib.pyplot as plt
import logging
import toml
import traceback

from ..core.types import SimulationResult
from ..core.analyzer import SimulationAnalyzer
from ..core.sweep import SweepResults
from ..core.events import Event, InputBlockGenerated, InputBlockReceived

logger = logging.getLogger(__name__)

class IBDiffusionAnalyzer(SimulationAnalyzer):
    """Analyzes Input Block diffusion through the network"""
    
    name = "ib_diffusion"
    
    def analyze(self, result: SimulationResult) -> Dict[str, Any]:
        """Analyze IB diffusion from simulation output"""
        if not result.success:
            return {}
            
        try:
            # Load topology to get total stake
            topology_file = result.config.params.get('topology')
            if isinstance(topology_file, list):
                topology_file = topology_file[0]
            
            test_data_dir = result.config.base_config_path.parent
            topology_path = test_data_dir / topology_file
            
            if not topology_path.exists():
                raise FileNotFoundError(f"Topology file not found: {topology_path}")
            
            # Load topology file as TOML
            with open(topology_path) as f:
                topology = toml.load(f)
                
            # Extract nodes from TOML structure
            nodes = topology.get('nodes', [])
            total_stake = sum(float(node.get('stake', 0)) for node in nodes)
            
            # Process events
            times = []
            stake_fractions = []
            current_stake = 0
            seen_nodes = set()  # Track nodes that have received the IB
            ib_generated = 0
            ib_received = 0
            
            with open(result.config.output_file) as f:
                for line in f:
                    try:
                        event = Event.from_json(line)
                        
                        # Track IB generation
                        if isinstance(event, InputBlockGenerated):
                            ib_generated += 1
                            
                        # Track IB receipts
                        elif isinstance(event, InputBlockReceived):
                            ib_received += 1
                            node_id = event.recipient
                            
                            if node_id not in seen_nodes:
                                seen_nodes.add(node_id)
                                
                                # Find node's stake
                                if node_id < len(nodes):
                                    node = nodes[node_id]
                                    stake = float(node.get('stake', 0))
                                    
                                    # Add to current stake and record time
                                    current_stake += stake
                                    stake_fraction = current_stake / total_stake
                                    
                                    times.append(event.time.as_seconds())
                                    stake_fractions.append(stake_fraction)
                                
                    except (json.JSONDecodeError, KeyError, IndexError) as e:
                        logger.debug(f"Error processing event: {e}")
                        continue
            
            metrics = {
                'times': times,
                'stake_fractions': stake_fractions,
                'ib_generation_probability': result.config.params['ib_generation_probability']
            }
            
            # Store metrics in result object
            result.metrics[self.name] = metrics
            
            return metrics
            
        except Exception as e:
            logger.error(f"Failed to analyze simulation {result.config.iteration}:")
            logger.error(traceback.format_exc())
            return {}
    
    def visualize(self, results: SweepResults) -> None:
        """Generate visualization of IB diffusion progress"""
        try:
            plt.figure(figsize=(12, 8))
            
            # Plot each simulation
            has_data = False
            colors = plt.cm.Set2(np.linspace(0, 1, len(results.successful_results())))
            
            for i, result in enumerate(results.successful_results()):
                metrics = result.metrics.get(self.name, {})
                logger.debug(f"Plotting metrics for simulation {i}: {metrics.keys()}")
                
                times = metrics.get('times', [])
                stake_fractions = metrics.get('stake_fractions', [])
                
                if not times or not stake_fractions:
                    logger.warning(f"No data to plot for simulation {i}")
                    continue
                
                # Add origin point
                times = [0.0] + times
                stake_fractions = [0.0] + stake_fractions
                
                # Sort points by time
                points = sorted(zip(times, stake_fractions))
                times_sorted, fractions_sorted = zip(*points)
                
                # Plot scatter points
                plt.scatter(times_sorted, fractions_sorted,
                          alpha=0.6, 
                          color=colors[i],
                          s=30,
                          label=f'sim-{result.config.iteration:04d}')
                
                # Fit logistic function if we have enough points
                if len(times_sorted) > 3:
                    from scipy.optimize import curve_fit
                    
                    def logistic(x, L, k, x0):
                        return L / (1 + np.exp(-k * (x - x0)))
                    
                    try:
                        # Initial parameter guesses
                        L_guess = 1.0  # Target full stake coverage
                        k_guess = 1.0  # Growth rate
                        x0_guess = np.mean(times_sorted)  # Midpoint
                        p0 = [L_guess, k_guess, x0_guess]
                        
                        # Create weights to emphasize higher stake fractions
                        weights = np.array(fractions_sorted) + 0.1  # Add small offset to avoid zero weights
                        
                        # Fit curve with bounds and weights
                        bounds = ([0.9, 0, 0], [1.0, np.inf, np.inf])  # Force L close to 1.0
                        popt, _ = curve_fit(logistic, times_sorted, fractions_sorted, 
                                          p0=p0, bounds=bounds, sigma=1/weights)
                        
                        # Generate points for smooth curve
                        x_fit = np.linspace(0, max(times_sorted), 100)
                        y_fit = logistic(x_fit, *popt)
                        
                        # Plot fitted curve
                        plt.plot(x_fit, y_fit, '--', 
                               color=colors[i], 
                               alpha=0.5,
                               linewidth=1)
                        
                        logger.debug(f"Fit parameters for sim {result.config.iteration}: L={popt[0]:.3f}, k={popt[1]:.3f}, x0={popt[2]:.3f}")
                    except RuntimeError:
                        logger.warning(f"Could not fit curve for simulation {result.config.iteration}")
                
                has_data = True
            
            if not has_data:
                logger.warning("No data to plot for any simulation")
                return
                
            plt.xlabel('Time (seconds)')
            plt.ylabel('Stake Fraction Reached')
            plt.title('Input Block Diffusion Progress')
            plt.grid(True, alpha=0.3)
            plt.ylim(0, 1)
            plt.xlim(left=0)
            plt.legend()
            
            # Save plot
            plot_path = results.output_dir / "plots"
            plot_path.mkdir(parents=True, exist_ok=True)
            plot_file = plot_path / "ib_diffusion.png"
            plt.savefig(plot_file, bbox_inches='tight')
            plt.close()
            
        except Exception as e:
            logger.error("Failed to generate visualization:")
            logger.error(traceback.format_exc())
            raise