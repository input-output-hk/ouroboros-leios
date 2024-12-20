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
            seen_nodes = set()
            ib_generated = 0
            ib_received = 0
            last_time = 0
            
            # Track node details for debugging
            node_details = []
            
            with open(result.config.output_file) as f:
                for line in f:
                    try:
                        event = Event.from_json(line)
                        
                        if isinstance(event, InputBlockGenerated):
                            ib_generated += 1
                            logger.debug(f"IB Generated at {event.time.as_seconds():.2f}s")
                            
                        elif isinstance(event, InputBlockReceived):
                            ib_received += 1
                            node_id = event.recipient
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
                                        logger.warning(f"Node {node_id} received IB at {event_time:.2f}s with stake {stake:e}")
                                        # Log the last few nodes before the gap
                                        logger.warning("Last 3 nodes before gap:")
                                        for detail in node_details[-4:-1]:
                                            logger.warning(f"  Node {detail['node_id']} at {detail['time']:.2f}s with stake {detail['stake']:e}")
                                    
                                    times.append(event_time)
                                    stake_fractions.append(stake_fraction)
                                    last_time = event_time
                                    
                                    logger.debug(f"Node {node_id} received IB at {event_time:.2f}s, "
                                               f"stake fraction now {stake_fraction:.2%}")
                                
                    except (json.JSONDecodeError, KeyError, IndexError) as e:
                        logger.debug(f"Error processing event: {e}")
                        continue
            
            # Log summary statistics
            logger.info(f"Time range: {min(times):.2f}s to {max(times):.2f}s")
            logger.info(f"Stake fraction range: {min(stake_fractions):.2%} to {max(stake_fractions):.2%}")
            logger.info(f"Total events: {len(times)} ({ib_generated} generated, {ib_received} received)")
            
            # Log distribution of time gaps
            time_gaps = [d['time_gap'] for d in node_details[1:]]  # Skip first node
            logger.info(f"Time gap statistics:")
            logger.info(f"  Mean: {np.mean(time_gaps):.3f}s")
            logger.info(f"  Median: {np.median(time_gaps):.3f}s")
            logger.info(f"  Max: {np.max(time_gaps):.3f}s")
            logger.info(f"  95th percentile: {np.percentile(time_gaps, 95):.3f}s")
            
            metrics = {
                'times': times,
                'stake_fractions': stake_fractions,
                'ib_generation_probability': result.config.params['ib_generation_probability']
            }
            
            # Store metrics in result object
            result.metrics[self.name] = metrics
            
            # Analyze network topology for outlier node
            links = topology.get('links', [])
            node_connections = {}
            
            # Count connections per node
            for link in links:
                nodes = link.get('nodes', [])
                if len(nodes) == 2:
                    for node in nodes:
                        node_connections[node] = node_connections.get(node, 0) + 1
            
            # Log connectivity for suspicious nodes
            logger.info(f"Node 97 connections: {node_connections.get(97, 0)}")
            logger.info(f"Average node connections: {np.mean(list(node_connections.values())):.1f}")
            
            # Log node's peers
            node_97_peers = [link['nodes'] for link in links if 97 in link.get('nodes', [])]
            logger.info(f"Node 97 peers: {node_97_peers}")
            
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
                
                # Sort points and log any potential outliers
                points = sorted(zip(times, stake_fractions))
                for t, f in points:
                    if t > 20:  # Suspicious time value
                        logger.warning(f"Suspicious data point in sim {result.config.iteration}: time={t:.2f}s, fraction={f:.2%}")
                
                times_sorted, fractions_sorted = zip(*points)
                
                # Filter out points beyond reasonable time range
                max_time = min(20, max(times_sorted))  # Use 20s or max time, whichever is smaller
                valid_points = [(t, f) for t, f in points if t <= max_time]
                if len(valid_points) < len(points):
                    logger.warning(f"Filtered out {len(points) - len(valid_points)} outlier points")
                
                if valid_points:
                    times_filtered, fractions_filtered = zip(*valid_points)
                else:
                    continue
                
                # Plot scatter points
                plt.scatter(times_filtered, fractions_filtered,
                          alpha=0.6, 
                          color=colors[i],
                          s=30,
                          label=f'sim-{result.config.iteration:04d}')
                
                # Fit logistic function if we have enough points
                if len(times_filtered) > 3:
                    from scipy.optimize import curve_fit
                    
                    def logistic(x, L, k, x0):
                        return L / (1 + np.exp(-k * (x - x0)))
                    
                    try:
                        # Initial parameter guesses
                        L_guess = 1.0  # Target full stake coverage
                        k_guess = 1.0  # Growth rate
                        x0_guess = np.mean(times_filtered)  # Midpoint
                        p0 = [L_guess, k_guess, x0_guess]
                        
                        # Create weights to emphasize higher stake fractions
                        weights = np.array(fractions_filtered) + 0.1
                        
                        # Fit curve with bounds and weights
                        bounds = ([0.9, 0, 0], [1.0, np.inf, np.inf])
                        popt, _ = curve_fit(logistic, times_filtered, fractions_filtered, 
                                          p0=p0, bounds=bounds, sigma=1/weights)
                        
                        # Generate points for smooth curve
                        x_fit = np.linspace(0, max(times_filtered), 100)
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