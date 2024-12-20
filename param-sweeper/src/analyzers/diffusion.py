from typing import Dict, Any, List, Tuple
import json
import numpy as np
import matplotlib.pyplot as plt
import logging
import toml
import traceback
from pathlib import Path

from ..core.types import SimulationResult
from ..core.analyzer import SimulationAnalyzer
from ..core.sweep import SweepResults
from ..core.events import Event

logger = logging.getLogger(__name__)

class BaseDiffusionAnalyzer(SimulationAnalyzer):
    """Base analyzer for measuring block/vote diffusion through the network"""
    
    def __init__(self, block_type: str, gen_param: str):
        """Initialize the diffusion analyzer
        
        Args:
            block_type: Type of block/vote to analyze (e.g. InputBlock, EndorserBlock)
            gen_param: Parameter controlling generation probability
        """
        self.block_type = block_type
        self.gen_param = gen_param
        self.name = f"{block_type.lower()}_diffusion"
    
    @staticmethod
    def create_combined_chart(results: SweepResults, analyzers: List['BaseDiffusionAnalyzer']) -> None:
        """Generate a combined visualization of all block types' diffusion progress
        
        Args:
            results: The sweep results containing metrics from all analyzers
            analyzers: List of diffusion analyzers to include in the chart
        """
        try:
            plt.figure(figsize=(12, 8))
            
            # Use a different color for each block type
            colors = plt.cm.Set2(np.linspace(0, 1, len(analyzers)))
            
            # Track overall min/max for better axis limits
            overall_min_time = float('inf')
            overall_max_time = 0
            
            # Get total slots and stage length from first simulation's config
            successful_results = results.successful_results()
            if not successful_results:
                logger.warning("No successful simulations to plot")
                return
                
            total_slots = successful_results[0].config.params.get('slots', 50)
            stage_length = successful_results[0].config.params.get('stage_length', 20)
            
            # Plot each block type
            for i, analyzer in enumerate(analyzers):
                color = colors[i]
                
                # Get metrics from first successful simulation
                metrics = successful_results[0].metrics.get(analyzer.name, {})
                times = metrics.get('times', [])
                stake_fractions = metrics.get('stake_fractions', [])
                
                if not times or not stake_fractions:
                    logger.warning(f"No data to plot for {analyzer.block_type}")
                    continue
                
                # Sort points by time
                points = sorted(zip(times, stake_fractions))
                times_sorted, fractions_sorted = zip(*points)
                
                # Update overall min/max
                overall_min_time = min(overall_min_time, min(times_sorted))
                overall_max_time = max(overall_max_time, max(times_sorted))
                
                # Plot diffusion progress
                plt.plot(times_sorted, 
                        [f * 100 for f in fractions_sorted],  # Convert to percentage
                        color=color,
                        label=analyzer.block_type,
                        marker='o',
                        markersize=4,
                        alpha=0.7)
            
            # Add small padding to axis limits
            time_padding = total_slots * 0.05  # 5% padding based on total slots
            
            plt.xlabel('Time (seconds)')
            plt.ylabel('Stake Reached (%)')
            plt.title('Message Diffusion')
            plt.grid(True, alpha=0.3)
            
            # Set axis limits with padding - ensure x axis extends to at least total_slots
            plt.xlim(0, max(total_slots, overall_max_time) + time_padding)
            plt.ylim(0, 105)  # 0-100% with small padding
            
            # Add stage lengths for each stage - one stage per stage_length slots
            num_stages = total_slots // stage_length
            for stage in range(num_stages + 1):
                stage_boundary = stage * stage_length  # Each slot is 1 second
                plt.axvline(x=stage_boundary, color='red', linestyle='--', alpha=0.3,
                          label='Stage Length' if stage == 0 else "")
            
            # Add text to show stage length in slots
            plt.text(0.02, 0.98, f'Stage Length: {stage_length} slots',
                    transform=plt.gca().transAxes, verticalalignment='top')
            
            # Add legend
            plt.legend(bbox_to_anchor=(1.05, 1), loc='upper left')
            
            # Save plot with extra space for legend
            plot_path = results.output_dir / "plots"
            plot_path.mkdir(parents=True, exist_ok=True)
            plot_file = plot_path / "combined_diffusion.png"
            plt.savefig(plot_file, bbox_inches='tight', dpi=300)
            plt.close()
            
        except Exception as e:
            logger.error("Failed to generate combined visualization:")
            logger.error(traceback.format_exc())
            raise
    
    def analyze(self, result: SimulationResult) -> Dict[str, Any]:
        """Analyze block diffusion from simulation output"""
        if not result.success:
            return {}
            
        try:
            # Load topology to get total stake
            topology_file = result.config.params.get('topology')
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
            sent_times = []  # Track when blocks are sent
            times = []  # Track when blocks are received
            stake_fractions = []
            current_stake = 0
            seen_nodes = set()
            blocks_sent = 0
            blocks_received = 0
            last_time = 0
            
            # Track node details for debugging
            node_details = []
            
            logger.info(f"Starting to process events for {self.block_type}")
            logger.info(f"Looking for event types: {self.block_type}Sent and {self.block_type}Received")
            
            with open(result.config.output_file) as f:
                for line in f:
                    try:
                        event = Event.from_json(line)
                        event_type = event.message.get('type')
                        
                        if event_type == f"{self.block_type}Sent":
                            blocks_sent += 1
                            sent_time = event.time.as_seconds()
                            sent_times.append(sent_time)
                            logger.debug(f"{self.block_type} Sent at {sent_time:.2f}s")
                            
                        elif event_type == f"{self.block_type}Received":
                            blocks_received += 1
                            node_id = event.message.get('recipient')
                            event_time = event.time.as_seconds()
                            
                            if node_id not in seen_nodes:
                                seen_nodes.add(node_id)
                                
                                if node_id < len(nodes):
                                    node = nodes[node_id]
                                    stake = float(node.get('stake', 0))
                                    current_stake += stake
                                    stake_fraction = current_stake / total_stake
                                    
                                    # Track node details
                                    node_details.append({
                                        'node_id': node_id,
                                        'time': event_time,
                                        'stake': stake,
                                        'stake_fraction': stake_fraction,
                                        'time_gap': event_time - last_time if times else 0
                                    })
                                    
                                    # Log suspicious time jumps
                                    if times and event_time - last_time > 5:
                                        logger.warning(f"Large time gap: {event_time - last_time:.2f}s between events")
                                        logger.warning(f"Node {node_id} received {self.block_type} at {event_time:.2f}s with stake {stake:e}")
                                        # Log the last few nodes before the gap
                                        logger.warning("Last 3 nodes before gap:")
                                        for detail in node_details[-4:-1]:
                                            logger.warning(f"  Node {detail['node_id']} at {detail['time']:.2f}s with stake {detail['stake']:e}")
                                    
                                    times.append(event_time)
                                    stake_fractions.append(stake_fraction)
                                    last_time = event_time
                                    
                                    logger.debug(f"Node {node_id} received {self.block_type} at {event_time:.2f}s, "
                                               f"stake fraction now {stake_fraction:.2%}")
                                
                    except (json.JSONDecodeError, KeyError, IndexError) as e:
                        logger.debug(f"Error processing event: {e}")
                        continue
            
            if not times:
                logger.warning(f"No {self.block_type} events found")
                logger.warning(f"Sent events: {blocks_sent}, Received events: {blocks_received}")
                return {}
            
            # Log summary statistics
            logger.info(f"Time range: {min(times):.2f}s to {max(times):.2f}s")
            logger.info(f"Sent time range: {min(sent_times):.2f}s to {max(sent_times):.2f}s")
            logger.info(f"Stake fraction range: {min(stake_fractions):.2%} to {max(stake_fractions):.2%}")
            logger.info(f"Total events: {len(times)} ({blocks_sent} sent, {blocks_received} received)")
            
            metrics = {
                'sent_times': sent_times,
                'times': times,
                'stake_fractions': stake_fractions,
                'generation_probability': result.config.params[self.gen_param]
            }
            
            # Store metrics in result object
            result.metrics[self.name] = metrics
            
            return metrics
            
        except Exception as e:
            logger.error(f"Failed to analyze simulation {result.config.iteration}:")
            logger.error(traceback.format_exc())
            return {}
    
    def visualize(self, results: SweepResults) -> None:
        """Generate visualization of block diffusion progress"""
        try:
            plt.figure(figsize=(12, 8))
            
            # Plot each simulation
            has_data = False
            colors = plt.cm.Set2(np.linspace(0, 1, len(results.successful_results())))
            
            # Track overall min/max for better axis limits
            overall_min_time = float('inf')
            overall_max_time = 0
            overall_max_fraction = 0
            
            for i, result in enumerate(results.successful_results()):
                metrics = result.metrics.get(self.name, {})
                logger.debug(f"Plotting metrics for simulation {i}: {metrics.keys()}")
                
                times = metrics.get('times', [])
                stake_fractions = metrics.get('stake_fractions', [])
                
                if not times or not stake_fractions:
                    logger.warning(f"No data to plot for simulation {i}")
                    continue
                
                # Sort points by time
                points = sorted(zip(times, stake_fractions))
                times_sorted, fractions_sorted = zip(*points)
                
                # Update overall min/max
                overall_min_time = min(overall_min_time, min(times_sorted))
                overall_max_time = max(overall_max_time, max(times_sorted))
                overall_max_fraction = max(overall_max_fraction, max(fractions_sorted))
                
                # Create label with relevant parameters
                gen_prob = result.config.params.get(self.gen_param, 'N/A')
                label = f'sim-{result.config.iteration:04d} ({self.gen_param}={gen_prob})'
                
                # Plot scatter points
                plt.scatter(times_sorted, fractions_sorted,
                          alpha=0.6, 
                          color=colors[i],
                          s=30,
                          label=label)
                
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
                        weights = np.array(fractions_sorted) + 0.1
                        
                        # Fit curve with bounds and weights
                        bounds = ([0.9, 0, 0], [1.0, np.inf, np.inf])
                        popt, _ = curve_fit(logistic, times_sorted, fractions_sorted, 
                                          p0=p0, bounds=bounds, sigma=1/weights)
                        
                        # Generate points for smooth curve
                        x_fit = np.linspace(min(times_sorted), max(times_sorted), 100)
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
            
            # Add small padding to axis limits
            time_padding = (overall_max_time - overall_min_time) * 0.05
            fraction_padding = (1.0 - overall_max_fraction) * 0.05
            
            plt.xlabel('Time (seconds)')
            plt.ylabel('Stake Fraction Reached')
            plt.title(f'{self.block_type} Diffusion Progress')
            plt.grid(True, alpha=0.3)
            
            # Set axis limits with padding
            plt.xlim(max(0, overall_min_time - time_padding), overall_max_time + time_padding)
            plt.ylim(0, min(1.0, overall_max_fraction + fraction_padding))
            
            # Adjust legend position to avoid overlap with data
            plt.legend(bbox_to_anchor=(1.05, 1), loc='upper left')
            
            # Save plot with extra space for legend
            plot_path = results.output_dir / "plots"
            plot_path.mkdir(parents=True, exist_ok=True)
            plot_file = plot_path / f"{self.name}.png"
            plt.savefig(plot_file, bbox_inches='tight', dpi=300)
            plt.close()
            
        except Exception as e:
            logger.error("Failed to generate visualization:")
            logger.error(traceback.format_exc())
            raise