from .diffusion import BaseDiffusionAnalyzer
import logging
from typing import Dict, Any
from ..core.types import SimulationResult
from ..core.events import Event
import toml
import json
import traceback

logger = logging.getLogger(__name__)

class VoteDiffusionAnalyzer(BaseDiffusionAnalyzer):
    """Analyzer for vote diffusion through the network"""
    
    name = "vote_diffusion"
    
    def __init__(self):
        """Initialize the vote diffusion analyzer"""
        super().__init__(block_type="Votes", gen_param="vote_probability")
    
    def analyze(self, result: SimulationResult) -> Dict[str, Any]:
        """Analyze vote diffusion from simulation output"""
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
            sent_times = []  # Track when votes are sent
            times = []  # Track when votes are received
            stake_fractions = []
            current_stake = 0
            seen_nodes = set()
            votes_sent = 0
            votes_received = 0
            last_time = 0
            
            # Track node details for debugging
            node_details = []
            
            logger.info("Starting to process vote events")
            logger.info("Looking for event types: VOTE_SENT and VOTE_RECEIVED")
            
            with open(result.config.output_file) as f:
                for line in f:
                    try:
                        event = Event.from_json(line)
                        event_type = event.message.get('type')
                        
                        if event_type == "VOTE_SENT":
                            votes_sent += 1
                            sent_time = event.time.as_seconds()
                            sent_times.append(sent_time)
                            logger.debug(f"Vote Sent at {sent_time:.2f}s")
                            
                        elif event_type == "VOTE_RECEIVED":
                            votes_received += 1
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
                                        logger.warning(f"Large time gap: {event_time - last_time:.2f}s between vote events")
                                        logger.warning(f"Node {node_id} received votes at {event_time:.2f}s with stake {stake:e}")
                                        # Log the last few nodes before the gap
                                        logger.warning("Last 3 nodes before gap:")
                                        for detail in node_details[-4:-1]:
                                            logger.warning(f"  Node {detail['node_id']} at {detail['time']:.2f}s with stake {detail['stake']:e}")
                                    
                                    times.append(event_time)
                                    stake_fractions.append(stake_fraction)
                                    last_time = event_time
                                    
                                    logger.debug(f"Node {node_id} received votes at {event_time:.2f}s, "
                                               f"stake fraction now {stake_fraction:.2%}")
                                
                    except (json.JSONDecodeError, KeyError, IndexError) as e:
                        logger.debug(f"Error processing event: {e}")
                        continue
            
            if not times:
                logger.warning("No vote events found")
                logger.warning(f"Sent events: {votes_sent}, Received events: {votes_received}")
                return {}
            
            # Log summary statistics
            logger.info(f"Time range: {min(times):.2f}s to {max(times):.2f}s")
            logger.info(f"Sent time range: {min(sent_times):.2f}s to {max(sent_times):.2f}s")
            logger.info(f"Stake fraction range: {min(stake_fractions):.2%} to {max(stake_fractions):.2%}")
            logger.info(f"Total events: {len(times)} ({votes_sent} sent, {votes_received} received)")
            
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
            logger.error("Failed to analyze vote diffusion:")
            logger.error(traceback.format_exc())
            return {} 