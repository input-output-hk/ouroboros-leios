from typing import Dict, Any, List, Optional, Set, DefaultDict
from collections import defaultdict
import numpy as np
import matplotlib.pyplot as plt
import logging
import json
import toml
import traceback
from pathlib import Path
from ..core.analyzer import SimulationAnalyzer
from ..core.sweep import SweepResults
from ..core.events import EventType
from ..core.types import SimulationResult
from ..core.time import VirtualTime

# Get logger
logger = logging.getLogger(__name__)

class BaseDiffusionAnalyzer(SimulationAnalyzer):
    """Base class for analyzing message diffusion through the network"""
    
    def __init__(self, block_type: str, gen_param: str, 
                 sent_type: EventType, received_type: EventType):
        """Initialize analyzer with message type and event types"""
        self.block_type = block_type
        self.gen_param = gen_param
        self.sent_type = sent_type
        self.received_type = received_type
        self.name = f"{block_type.lower()}_diffusion"
        
    def analyze(self, result: SimulationResult) -> Dict[str, Any]:
        """Analyze message diffusion from simulation output"""
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
            
            # Create node stake lookup, only for nodes that have stake
            node_stakes = {}
            total_stake = 0
            for i, node in enumerate(nodes):
                stake = node.get('stake')
                if stake is not None:  # Only include nodes that have stake defined
                    node_id = str(i)  # Node IDs are their indices
                    node_stakes[node_id] = float(stake)
                    total_stake += float(stake)
            
            logger.debug(f"Total stake in network: {total_stake}")
            logger.debug(f"Node stakes: {node_stakes}")
            
            # Track per-message propagation
            message_propagation = defaultdict(lambda: {
                'producer': None,  # Producer node ID
                'first_sent_time': None,  # Time of first sent event from producer
                'hops': [],  # List of propagation hops
                'node_coverage': defaultdict(lambda: {  # Per-node reception details
                    'first_received': None,  # First time node received the message
                    'received_from': None,  # Node ID that sent the message
                    'propagation_time': None,  # Time from sender's sent to receiver's received
                    'stake': 0.0  # Node's stake
                })
            })
            
            messages_sent = 0
            messages_received = 0
            
            # First pass: Record all sent events and identify producers
            sent_events = defaultdict(list)  # msg_id -> [(time, sender, recipient), ...]
            producers = {}  # msg_id -> producer_id
            
            # Track all unique message IDs we see
            all_msg_ids = set()
            
            for event in result.events:
                if event.type == self.sent_type.value:
                    msg_id = event.get_message_id()
                    if msg_id is None:
                        continue
                    
                    all_msg_ids.add(msg_id)
                    sender = event.data.get('sender')
                    recipient = event.data.get('recipient')
                    if sender is not None and recipient is not None:
                        sent_events[msg_id].append({
                            'time': VirtualTime(event.time),
                            'sender': sender,
                            'recipient': recipient
                        })
                        messages_sent += 1
                        
                        # Track the first sender as the producer
                        if msg_id not in producers:
                            producers[msg_id] = sender
                            message_propagation[msg_id]['producer'] = sender
                            message_propagation[msg_id]['first_sent_time'] = VirtualTime(event.time).as_seconds()
                            logger.debug(f"{self.block_type} {msg_id} produced by node {sender}")
            
            logger.debug(f"Found {len(all_msg_ids)} unique message IDs: {sorted(all_msg_ids)}")
            logger.debug(f"Producers: {producers}")
            
            # Second pass: Match received events with sent events
            for event in result.events:
                if event.type == self.received_type.value:
                    msg_id = event.get_message_id()
                    if msg_id is None:
                        continue
                    
                    recipient = event.data.get('recipient')
                    sender = event.data.get('sender')
                    if recipient is None or sender is None:
                        continue
                    
                    received_time = VirtualTime(event.time)
                    
                    # Find matching sent event
                    matching_sent = None
                    for sent in sent_events[msg_id]:
                        if sent['sender'] == sender and sent['recipient'] == recipient:
                            matching_sent = sent
                            break
                    
                    if matching_sent is None:
                        logger.debug(f"No matching sent event found for {self.block_type} {msg_id} from {sender} to {recipient}")
                        continue
                        
                    messages_received += 1
                    
                    # Get recipient stake
                    recipient_stake = node_stakes.get(str(recipient), 0.0)
                    
                    # Calculate propagation time
                    prop_time = received_time - matching_sent['time']
                    
                    # Update node coverage
                    node_data = message_propagation[msg_id]['node_coverage'][recipient]
                    if node_data['first_received'] is None or received_time.as_seconds() < node_data['first_received']:
                        node_data['first_received'] = received_time.as_seconds()
                        node_data['received_from'] = sender
                        node_data['propagation_time'] = prop_time.as_seconds()
                        node_data['stake'] = recipient_stake
                    
                    # Record hop details
                    message_propagation[msg_id]['hops'].append({
                        'sender': sender,
                        'recipient': recipient,
                        'sent_time': matching_sent['time'].as_seconds(),
                        'received_time': received_time.as_seconds(),
                        'propagation_time': prop_time.as_seconds(),
                        'recipient_stake': recipient_stake,
                        'stake_fraction': recipient_stake / total_stake if total_stake > 0 else 0,
                        'is_producer': sender == producers.get(msg_id, None)
                    })
                    
                    logger.debug(f"{self.block_type} {msg_id} sent from {sender} to {recipient} in {prop_time.as_seconds():.3f}s")
            
            # Log node coverage for each message
            for msg_id, data in message_propagation.items():
                logger.debug(f"\nNode coverage for {self.block_type} {msg_id}:")
                logger.debug(f"Producer: {data['producer']}")
                logger.debug(f"First sent time: {data['first_sent_time']}")
                logger.debug(f"Nodes covered: {sorted(data['node_coverage'].keys())}")
                total_covered_stake = sum(coverage['stake'] for coverage in data['node_coverage'].values())
                logger.debug(f"Total stake covered: {total_covered_stake} ({(total_covered_stake/total_stake)*100:.1f}%)")
            
            # Calculate statistics
            stats = {
                'total_messages_sent': messages_sent,
                'total_messages_received': messages_received,
                'unique_messages': len(message_propagation)
            }
            
            # Create metrics dictionary
            metrics = {
                'message_propagation': {
                    msg_id: {
                        'producer': producers.get(msg_id),
                        'first_sent_time': data['first_sent_time'],
                        'hops': data['hops'],
                        'node_coverage': {
                            node_id: {
                                'first_received': coverage['first_received'],
                                'received_from': coverage['received_from'],
                                'propagation_time': coverage['propagation_time'],
                                'stake': coverage['stake']
                            } for node_id, coverage in data['node_coverage'].items()
                        }
                    } for msg_id, data in message_propagation.items()
                },
                'stats': stats
            }
            
            # Store metrics in result object
            result.metrics[self.name] = metrics
            
            logger.info(f"{self.block_type} diffusion: {stats['unique_messages']} messages, {stats['total_messages_sent']} sent, {stats['total_messages_received']} received")
            
            return metrics
            
        except Exception as e:
            logger.error(f"Failed to analyze {self.block_type} diffusion:")
            logger.error(traceback.format_exc())
            return {}
    
    def visualize(self, results: SweepResults) -> None:
        """Generate visualization of message diffusion"""
        try:
            # Create single figure
            fig, ax = plt.subplots(figsize=(10, 6))
            
            # Track if we've plotted anything
            plotted_any = False
            
            # Collect all diffusion curves
            all_curves = []
            
            # Plot individual message diffusion curves
            for result in results.successful_results():
                metrics = result.metrics.get(self.name, {})
                message_propagation = metrics.get('message_propagation', {})
                
                logger.debug(f"Found {len(message_propagation)} messages to process")
                
                for msg_id, data in message_propagation.items():
                    # Get the producer ID and first sent time
                    producer_id = data.get('producer')
                    first_sent = data.get('first_sent_time')
                    if producer_id is None or first_sent is None:
                        logger.debug(f"Missing producer or first sent time for {self.block_type} {msg_id}")
                        continue
                    
                    # Get node coverage data
                    node_coverage = data.get('node_coverage', {})
                    if not node_coverage:
                        logger.debug(f"No node coverage data for {self.block_type} {msg_id}")
                        continue
                    
                    # Calculate total stake covered
                    total_stake = sum(coverage['stake'] for coverage in node_coverage.values())
                    if total_stake <= 0:
                        logger.debug(f"No stake covered for {self.block_type} {msg_id}")
                        continue
                    
                    # Sort coverage by received time
                    sorted_coverage = sorted(
                        [(node_id, coverage) for node_id, coverage in node_coverage.items()],
                        key=lambda x: x[1]['first_received']
                    )
                    
                    # Calculate points for the diffusion curve
                    curve_points = [(0, 0)]  # Start at t=0, stake=0
                    
                    # Calculate cumulative stake coverage
                    current_stake = 0
                    for node_id, coverage in sorted_coverage:
                        if coverage['first_received'] is not None:
                            current_stake += coverage['stake']
                            time_since_first = coverage['first_received'] - first_sent
                            stake_percentage = (current_stake / total_stake) * 100
                            curve_points.append((time_since_first, stake_percentage))
                    
                    if len(curve_points) > 1:
                        all_curves.append(curve_points)
                        logger.debug(f"{self.block_type} {msg_id}: collected {len(curve_points)} points, max time={curve_points[-1][0]:.3f}s, final stake={curve_points[-1][1]:.1f}%")
            
            if not all_curves:
                logger.warning(f"No {self.block_type} diffusion curves were collected")
                return
            
            # Create common time points for interpolation
            max_time = max(point[0] for curve in all_curves for point in curve)
            time_points = np.linspace(0, max_time, num=100)
            
            # Interpolate each curve to the common time points
            interpolated_curves = []
            for curve in all_curves:
                times, stakes = zip(*curve)
                if len(times) > 1:  # Need at least 2 points for interpolation
                    interpolated_stakes = np.interp(time_points, times, stakes)
                    interpolated_curves.append(interpolated_stakes)
            
            if not interpolated_curves:
                logger.warning(f"No {self.block_type} curves could be interpolated")
                return
            
            # Calculate statistics
            interpolated_curves = np.array(interpolated_curves)
            mean_curve = np.mean(interpolated_curves, axis=0)
            std_curve = np.std(interpolated_curves, axis=0)
            
            # Plot mean curve with confidence band
            ax.plot(time_points, mean_curve, '-', color='blue', label='Mean Diffusion', linewidth=2)
            ax.fill_between(time_points, 
                          np.maximum(0, mean_curve - std_curve),  # Ensure lower bound doesn't go below 0
                          np.minimum(100, mean_curve + std_curve),  # Ensure upper bound doesn't exceed 100
                          color='blue', alpha=0.2, label='±1 Std Dev')
            
            # Configure plot
            ax.set_xlabel('Time since first sent (seconds)')
            ax.set_ylabel('Stake Reached (%)')
            ax.set_title(f'{self.block_type} Network Diffusion (n={len(all_curves)})')
            ax.grid(True, alpha=0.3)
            ax.legend(loc='lower right')
            
            # Ensure y-axis goes from 0 to 100
            ax.set_ylim(0, 100)
            
            # Add some padding to x-axis
            ax.set_xlim(0, max_time * 1.1)
            
            # Save plot
            plot_path = results.output_dir / "plots"
            plot_path.mkdir(parents=True, exist_ok=True)
            plot_file = plot_path / f"{self.name}.png"
            plt.savefig(plot_file, bbox_inches='tight', dpi=300)
            plt.close()
            
            logger.info(f"Generated {self.block_type} diffusion visualization")
            
        except Exception as e:
            logger.error("Failed to generate propagation visualization:")
            logger.error(traceback.format_exc())
            raise