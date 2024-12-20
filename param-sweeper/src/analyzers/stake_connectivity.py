from typing import Dict, List, Any
import numpy as np
import matplotlib.pyplot as plt
from pathlib import Path
import logging
import toml
import traceback
from collections import defaultdict

from ..core import SimulationAnalyzer
from ..core.sweep import SweepResults
from ..core.types import SimulationResult

logger = logging.getLogger(__name__)

class StakeConnectivityAnalyzer(SimulationAnalyzer):
    """Analyzes stake distribution and network connectivity patterns."""
    
    name = "stake_connectivity"
    
    def analyze(self, result: SimulationResult) -> Dict[str, Any]:
        """Analyze network topology and stake distribution metrics"""
        if not result.success:
            return {}
            
        try:
            # Load topology
            topology_file = result.config.params.get('topology')
            
            test_data_dir = result.config.base_config_path.parent
            topology_path = test_data_dir / topology_file
            
            with open(topology_path) as f:
                topology = toml.load(f)
            
            # Extract network structure
            nodes = topology.get('nodes', [])
            links = topology.get('links', [])
            
            # Build adjacency map
            adjacency = defaultdict(list)
            for link in links:
                n1, n2 = link.get('nodes', [])
                adjacency[n1].append(n2)
                adjacency[n2].append(n1)
            
            # Calculate metrics
            producer_metrics = self.calculate_producer_metrics(nodes, adjacency)
            
            # Calculate network-wide metrics
            total_producers = sum(1 for node in nodes if float(node.get('stake', 0)) > 0)
            total_relays = sum(1 for node in nodes if float(node.get('stake', 0)) == 0)
            
            relay_connections = [m['relay_connections'] for m in producer_metrics.values()]
            avg_relay_connections = np.mean(relay_connections) if relay_connections else 0
            
            metrics = {
                'total_producers': total_producers,
                'total_relays': total_relays,
                'avg_relay_connections': avg_relay_connections,
                'producer_metrics': producer_metrics
            }
            
            # Store metrics in result object
            result.metrics[self.name] = metrics
            
            return metrics
            
        except Exception as e:
            logger.error(f"Failed to analyze topology for simulation {result.config.iteration}:")
            logger.error(traceback.format_exc())
            return {}
    
    def calculate_producer_metrics(self, nodes: List[dict], adjacency: dict) -> Dict[int, Dict[str, Any]]:
        """Calculate producer-specific metrics"""
        # Identify producers and relays
        producers = {i: node for i, node in enumerate(nodes) if float(node.get('stake', 0)) > 0}
        relays = {i: node for i, node in enumerate(nodes) if float(node.get('stake', 0)) == 0}
        
        # Calculate producer-relay connectivity
        producer_metrics = {}
        for pid, producer in producers.items():
            # Find connected relays
            direct_relays = [n for n in adjacency[pid] if n in relays]
            
            # Find other producers reachable through these relays
            reachable_producers = set()
            for relay in direct_relays:
                for neighbor in adjacency[relay]:
                    if neighbor in producers and neighbor != pid:
                        reachable_producers.add(neighbor)
            
            producer_metrics[pid] = {
                'stake': float(producer.get('stake', 0)),
                'relay_connections': len(direct_relays),
                'reachable_producers': len(reachable_producers),
                'relay_isolation': len(direct_relays) == 0,
                'direct_producer_connections': sum(1 for n in adjacency[pid] if n in producers)
            }
        
        return producer_metrics
    
    def generate_topology_report(self, metrics: Dict[str, Any], output_dir: Path) -> None:
        """Generate a detailed report of topology issues"""
        try:
            producer_metrics = metrics.get('producer_metrics', {})
            if not producer_metrics:
                logger.warning("No producer metrics available for report")
                return
                
            relay_connections = [m['relay_connections'] for m in producer_metrics.values()]
            mean_relays = np.mean(relay_connections) if relay_connections else 0
            std_relays = np.std(relay_connections) if relay_connections else 0
            
            # Collect problematic nodes
            issues = []
            
            for node_id, m in producer_metrics.items():
                node_issues = []
                
                if m['direct_producer_connections'] > 0:
                    node_issues.append(
                        f"Direct producer connections: {m['direct_producer_connections']} "
                        f"(security risk - producers should connect via relays)"
                    )
                
                if m['relay_connections'] < mean_relays - std_relays:
                    node_issues.append(
                        f"Low relay connectivity: {m['relay_connections']} connections "
                        f"(below average of {mean_relays:.1f})"
                    )
                
                if m['relay_isolation']:
                    node_issues.append("No relay connections (node is isolated)")
                
                if node_issues:
                    issues.append({
                        'node_id': node_id,
                        'stake': m['stake'],
                        'issues': node_issues,
                        'metrics': {
                            'relay_connections': m['relay_connections'],
                            'reachable_producers': m['reachable_producers'],
                            'direct_producer_connections': m['direct_producer_connections']
                        }
                    })
            
            # Sort issues by stake (highest stake first)
            issues.sort(key=lambda x: x['stake'], reverse=True)
            
            # Generate report
            report_path = output_dir / "topology_issues.md"
            with open(report_path, 'w') as f:
                f.write("# Network Topology Issues Report\n\n")
                
                f.write("## Network Overview\n\n")
                # Create network overview table
                f.write("| Metric | Value |\n")
                f.write("|--------|-------|\n")
                f.write(f"| Total Producers | {metrics.get('total_producers', 0)} |\n")
                f.write(f"| Total Relays | {metrics.get('total_relays', 0)} |\n")
                f.write(f"| Average Relay Connections | {metrics.get('avg_relay_connections', 0):.1f} |\n")
                f.write("\n")
                
                f.write("## Problematic Nodes\n\n")
                if issues:
                    # Create table header for problematic nodes
                    f.write("| Node ID | Stake | Relay Connections | Reachable Producers | Direct Producer Connections | Issues |\n")
                    f.write("|---------|--------|------------------|--------------------|-----------------------------|--------|\n")
                    
                    for issue in issues:
                        issues_text = "<br>".join(issue['issues'])
                        metrics = issue['metrics']
                        f.write(f"| {issue['node_id']} | {issue['stake']:,} | {metrics['relay_connections']} | ")
                        f.write(f"{metrics['reachable_producers']} | {metrics['direct_producer_connections']} | {issues_text} |\n")
                else:
                    f.write("\nNo significant issues detected.\n")

        except Exception as e:
            logger.error(f"Failed to generate topology report: {str(e)}")
            logger.error(traceback.format_exc())

    def visualize(self, results: SweepResults) -> None:
        """Generate visualization of network topology metrics"""
        try:
            metrics = results.successful_results()[0].metrics.get(self.name, {})
            if not metrics:
                logger.warning("No topology metrics to visualize")
                return
            
            producer_metrics = metrics.get('producer_metrics', {})
            if not producer_metrics:
                logger.warning("No producer metrics available for visualization")
                return
            
            # Generate issues report
            self.generate_topology_report(metrics, results.output_dir)
            
            # Create figure with larger size
            plt.figure(figsize=(12, 8))
            
            # Extract data
            relay_connections = [m['relay_connections'] for m in producer_metrics.values()]
            stakes = [m['stake'] for m in producer_metrics.values()]
            reachable = [m['reachable_producers'] for m in producer_metrics.values()]
            
            # Create scatter plot with horizontal lines
            scatter = plt.scatter(relay_connections, stakes, 
                             c=reachable,  # Color by reachable producers
                             cmap='viridis',
                             alpha=0.8,
                             s=200,  # Large markers
                             marker='_',  # Horizontal lines
                             linewidth=2)  # Thick lines
            
            # Add grid with more emphasis on x-axis lines
            plt.grid(True, which='major', alpha=0.2)
            plt.grid(True, which='major', axis='x', alpha=0.4, linewidth=1)
            
            # Customize axes
            plt.xlabel('Number of Relay Connections')
            plt.ylabel('Node Stake')
            plt.yscale('log')
            
            # Set x-axis to show only integer values
            max_connections = max(relay_connections)
            plt.xlim(-0.5, max_connections + 0.5)
            plt.xticks(range(0, max_connections + 1))
            
            plt.title('Producer-Relay Connectivity vs Stake')
            cbar = plt.colorbar(scatter, label='Number of Reachable Producers (1-hop)')
            
            # Make colorbar ticks integers
            cbar.set_ticks(np.unique(reachable))
            
            plt.tight_layout()
            
            # Save plot
            plot_path = results.output_dir / "plots"
            plot_path.mkdir(parents=True, exist_ok=True)
            plot_file = plot_path / "topology_metrics.png"
            plt.savefig(plot_file, bbox_inches='tight', dpi=300)
            plt.close()
            
        except Exception as e:
            logger.error("Failed to generate visualization:")
            logger.error(traceback.format_exc())
            raise