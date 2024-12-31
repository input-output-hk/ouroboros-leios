from typing import Dict, Any, List
import numpy as np
import matplotlib.pyplot as plt
import logging
import json
import traceback
from ..core.analyzer import SimulationAnalyzer
from ..core.sweep import SweepResults
from ..core.events import EventType
from ..core.types import SimulationEvent, SimulationResult
from ..core.time import VirtualTime

logger = logging.getLogger(__name__)

class BaseProcessingTimeAnalyzer(SimulationAnalyzer):
    """Base class for analyzing message processing times"""
    
    def __init__(self, message_type: str, generated_type: EventType, sent_type: EventType):
        """Initialize analyzer with message type and event types"""
        self.message_type = message_type
        self.generated_type = generated_type
        self.sent_type = sent_type
        self.name = f"{message_type.lower()}_processing"
        
    def analyze(self, result: SimulationResult) -> Dict[str, Any]:
        """Analyze processing times from simulation output"""
        if not result.success:
            return {}
            
        try:
            # Track message processing times
            generated_times = {}  # id -> generation_time
            first_sent_times = {}  # id -> first_sent_time
            processing_times = {}  # id -> time between generated and first sent
            slots = {}  # id -> slot number
            
            logger.info(f"Starting to process {self.message_type} processing times")
            logger.info(f"Looking for event types: {self.generated_type.value} and {self.sent_type.value}")
            
            for event in result.events:
                try:
                    msg_id = event.get_message_id()
                    if msg_id is None:
                        continue
                        
                    if event.type == self.generated_type.value:
                        generated_times[msg_id] = VirtualTime(event.time)
                        slots[msg_id] = event.data.get('slot')
                        
                    elif event.type == self.sent_type.value:
                        if event.is_producer_event(msg_id) and msg_id not in first_sent_times:
                            first_sent_times[msg_id] = VirtualTime(event.time)
                            if msg_id in generated_times:
                                processing_times[msg_id] = (first_sent_times[msg_id] - generated_times[msg_id]).as_seconds()
                
                except (KeyError, IndexError) as e:
                    logger.debug(f"Error processing event: {e}")
                    continue
            
            if not processing_times:
                logger.warning(f"No {self.message_type} processing times found")
                return {}
            
            # Calculate statistics
            times = list(processing_times.values())
            stats = {
                'mean': np.mean(times),
                'median': np.median(times),
                'std': np.std(times),
                'min': np.min(times),
                'max': np.max(times),
                'count': len(times),
                'percentiles': {
                    '25': np.percentile(times, 25),
                    '75': np.percentile(times, 75),
                    '90': np.percentile(times, 90),
                    '95': np.percentile(times, 95),
                    '99': np.percentile(times, 99)
                }
            }
            
            # Log statistics
            logger.info(f"Processing time statistics for {self.message_type}:")
            logger.info(f"  Count: {stats['count']} messages")
            logger.info(f"  Mean: {stats['mean']:.3f}s")
            logger.info(f"  Median: {stats['median']:.3f}s")
            logger.info(f"  Std Dev: {stats['std']:.3f}s")
            logger.info(f"  Range: {stats['min']:.3f}s to {stats['max']:.3f}s")
            logger.info(f"  95th percentile: {stats['percentiles']['95']:.3f}s")
            
            metrics = {
                'processing_times': processing_times,
                'slots': slots,
                'stats': stats
            }
            
            # Store metrics in result object
            result.metrics[self.name] = metrics
            
            return metrics
            
        except Exception as e:
            logger.error(f"Failed to analyze {self.message_type} processing times:")
            logger.error(traceback.format_exc())
            return {}
    
    def visualize(self, results: SweepResults) -> None:
        """Generate visualization of processing times"""
        try:
            # Collect all processing times
            all_times = []
            all_slots = []
            
            for result in results.successful_results():
                metrics = result.metrics.get(self.name, {})
                processing_times = metrics.get('processing_times', {})
                slots = metrics.get('slots', {})
                
                for msg_id, time in processing_times.items():
                    all_times.append(time * 1000)  # Convert to milliseconds for visualization
                    all_slots.append(slots.get(msg_id, 0))
            
            if not all_times:
                logger.warning(f"No {self.message_type} processing times to plot")
                return
            
            plt.figure(figsize=(12, 6))
            
            # Create box plot
            plt.subplot(1, 2, 1)
            plt.boxplot(all_times, whis=[5, 95], showfliers=True)
            plt.ylabel('Processing Time (ms)')
            plt.title(f'{self.message_type} Processing Time Distribution')
            plt.grid(True, alpha=0.3)
            
            # Create histogram
            plt.subplot(1, 2, 2)
            plt.hist(all_times, bins=50, alpha=0.7)
            plt.xlabel('Processing Time (ms)')
            plt.ylabel('Count')
            plt.title(f'{self.message_type} Processing Time Histogram')
            plt.grid(True, alpha=0.3)
            
            # Adjust layout
            plt.tight_layout()
            
            # Save plot
            plot_path = results.output_dir / "plots"
            plot_path.mkdir(parents=True, exist_ok=True)
            plot_file = plot_path / f"{self.name}.png"
            plt.savefig(plot_file, bbox_inches='tight', dpi=300)
            plt.close()
            
            logger.info(f"Generated processing time visualization for {self.message_type}")
            
        except Exception as e:
            logger.error("Failed to generate processing time visualization:")
            logger.error(traceback.format_exc())
            raise