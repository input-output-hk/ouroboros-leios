from typing import Dict, Any, Set, List
import numpy as np
import matplotlib.pyplot as plt
import logging
import toml
import traceback
from adjustText import adjust_text
from collections import defaultdict, deque
from pathlib import Path

from ..core.analyzer import SimulationAnalyzer
from ..core.sweep import SweepResults
from ..core.types import SimulationResult
logger = logging.getLogger(__name__)

class TopologyAnalyzer(SimulationAnalyzer):
    """Analyzes network topology metrics"""
    
    name = "topology"
    
    def analyze(self, result: SimulationResult) -> Dict[str, Any]:
        """Analyze network topology metrics"""
        
        if not result.success:
            return {}
            
        try:
            # Load topology
            topology_file = result.config.params.get('topology')
            if isinstance(topology_file, list):
                topology_file = topology_file[0]
            
            test_data_dir = result.config.base_config_path.parent
            topology_path = test_data_dir / topology_file
            
            with open(topology_path) as f:
                topology = toml.load(f)
            
            # Calculate metrics
            metrics = self.calculate_metrics(topology)
            
            # Store metrics in result object
            result.metrics[self.name] = metrics
            
            return metrics
            
        except Exception as e:
            logger.error(f"Failed to analyze topology for simulation {result.config.iteration}:")
            logger.error(traceback.format_exc())
            return {}
    def calculate_metrics(self, topology: dict) -> Dict[str, Any]:
        """Calculate topology-aware network metrics"""
        nodes = topology.get('nodes', [])
        links = topology.get('links', [])
        
        # Build adjacency map
        adjacency = defaultdict(list)
        for link in links:
            n1, n2 = link.get('nodes', [])
            adjacency[n1].append(n2)
            adjacency[n2].append(n1)
        
        # Calculate basic metrics (existing code)
        producer_metrics = self.calculate_producer_metrics(nodes, adjacency)
        
        # Calculate advanced network metrics
        network_metrics = self.calculate_network_metrics(adjacency, nodes)
        
        return {
            'producer_metrics': producer_metrics,
            'network_metrics': network_metrics,
            'total_producers': len([n for n in nodes if float(n.get('stake', 0)) > 0]),
            'total_relays': len([n for n in nodes if float(n.get('stake', 0)) == 0]),
            'total_links': len(links),
            'avg_relay_connections': np.mean([m['relay_connections'] for m in producer_metrics.values()]),
            'producers_without_relays': sum(1 for m in producer_metrics.values() if m['relay_isolation'])
        }
    
    def calculate_network_metrics(self, adjacency: dict, nodes: List[dict]) -> Dict[str, float]:
        """Calculate advanced network metrics"""
        n = len(nodes)
        
        def calculate_clustering_coefficient(node_id: int) -> float:
            """Calculate local clustering coefficient for a node"""
            neighbors = adjacency[node_id]
            if len(neighbors) < 2:
                return 0.0
            
            possible_connections = len(neighbors) * (len(neighbors) - 1) / 2
            actual_connections = 0
            
            for i in range(len(neighbors)):
                for j in range(i + 1, len(neighbors)):
                    if neighbors[j] in adjacency[neighbors[i]]:
                        actual_connections += 1
            
            return actual_connections / possible_connections
        
        def calculate_average_path_length() -> float:
            """Calculate average shortest path length using BFS"""
            total_path_length = 0
            total_paths = 0
            
            for start in adjacency:
                # BFS for shortest paths
                distances = {}
                queue = deque([(start, 0)])
                visited = {start}
                
                while queue:
                    node, dist = queue.popleft()
                    distances[node] = dist
                    
                    for neighbor in adjacency[node]:
                        if neighbor not in visited:
                            visited.add(neighbor)
                            queue.append((neighbor, dist + 1))
                
                total_path_length += sum(distances.values())
                total_paths += len(distances) - 1  # Exclude path to self
            
            return total_path_length / (total_paths) if total_paths > 0 else 0
        
        # Calculate metrics
        clustering_coefficients = [calculate_clustering_coefficient(i) for i in range(n)]
        avg_clustering = np.mean(clustering_coefficients)
        
        # Network density
        max_edges = n * (n - 1) / 2
        actual_edges = sum(len(neighbors) for neighbors in adjacency.values()) / 2
        density = actual_edges / max_edges
        
        # Average path length
        avg_path_length = calculate_average_path_length()
        
        return {
            'avg_clustering_coefficient': avg_clustering,
            'network_density': density,
            'avg_path_length': avg_path_length,
            'max_clustering_coefficient': max(clustering_coefficients),
            'min_clustering_coefficient': min(clustering_coefficients)
        }
    
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
                
                # Only add network metrics if available
                network_metrics = metrics.get('network_metrics', {})
                if network_metrics:
                    f.write(f"| Network Density | {network_metrics.get('network_density', 0):.3f} |\n")
                    f.write(f"| Average Path Length | {network_metrics.get('avg_path_length', 0):.2f} |\n")
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
                
                # Add network metrics section if available
                if network_metrics:
                    f.write("\n## Detailed Network Metrics\n\n")
                    f.write("| Metric | Value |\n")
                    f.write("|--------|-------|\n")
                    for metric, value in network_metrics.items():
                        f.write(f"| {metric.replace('_', ' ').title()} | {value:.3f} |\n")

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
            
            # Create single plot with larger size
            plt.figure(figsize=(12, 8))
            
            # Plot: Producer-Relay Connectivity vs Stake
            relay_connections = [m['relay_connections'] for m in producer_metrics.values()]
            stakes = [m['stake'] for m in producer_metrics.values()]
            reachable = [m['reachable_producers'] for m in producer_metrics.values()]
            
            scatter = plt.scatter(relay_connections, stakes, 
                             c=reachable,  # Color by reachable producers
                             cmap='viridis',
                             alpha=0.7,
                             s=100)
            
            plt.xlabel('Number of Relay Connections')
            plt.ylabel('Node Stake')
            plt.yscale('log')
            plt.title('Producer-Relay Connectivity vs Stake')
            plt.grid(True, alpha=0.3)
            plt.colorbar(scatter, label='Number of Reachable Producers')
            
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