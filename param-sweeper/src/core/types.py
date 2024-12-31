from dataclasses import dataclass
from typing import Dict, Any, List, Optional, Union
from pathlib import Path
import json
from datetime import datetime

@dataclass
class SimulationConfig:
    """Configuration for a single simulation run"""
    params: Dict[str, Any]
    iteration: int
    output_dir: Path
    config_dir: Path
    sim_dir: Path
    base_config_path: Path
    
    @property
    def output_file(self) -> Path:
        """Path to simulation output file"""
        return self.sim_dir / f"sim_{self.iteration:04d}.jsonl"
    
    @property
    def config_file(self) -> Path:
        """Path to config file"""
        return self.config_dir / f"config_{self.iteration:04d}.toml"

@dataclass
class SimulationEvent:
    """Single event from simulation output"""
    time: float
    type: str
    data: Dict[str, Any]
    
    @classmethod
    def from_json(cls, line: str) -> 'SimulationEvent':
        """Create event from JSON line"""
        data = json.loads(line)
        return cls(
            time=data["time"],
            type=data["message"]["type"],
            data=data["message"]
        )
        
    def get_message_id(self) -> Optional[str]:
        """Get a consistent string message ID from the event data.
        
        For most events, this is the 'id' field.
        For PraosBlock events, this is 'slot-{slot}'.
        For Vote events with dictionary IDs, this is '{slot}-{producer}'.
        
        Returns:
            str: A consistent string ID for the message, or None if no ID could be determined
        """
        msg_id = self.data.get('id')
        
        # For PraosBlock events, use slot as ID
        if msg_id is None:
            slot = self.data.get('slot')
            if slot is not None:
                return f"slot-{slot}"
            return None
            
        # For Vote events with dictionary IDs
        if isinstance(msg_id, dict):
            if 'id' in msg_id:
                return msg_id['id']
            # Create a consistent string representation
            slot = msg_id.get('slot')
            producer = msg_id.get('producer')
            if slot is not None and producer is not None:
                return f"{slot}-{producer}"
            return None
            
        # For all other events, convert ID to string
        return str(msg_id)
        
    def is_producer_event(self, msg_id: str) -> bool:
        """Check if this event is from the message producer.
        
        For PraosBlock events, the sender is considered the producer.
        For other events, checks if sender matches producer.
        
        Args:
            msg_id: The message ID to check (needed to determine event type)
            
        Returns:
            bool: True if this is a producer event, False otherwise
        """
        if msg_id.startswith('slot-'):
            # For PraosBlock events, sender is the producer
            return True
        else:
            # For other events, check producer matches sender
            producer = self.data.get('producer')
            sender = self.data.get('sender')
            return producer == sender

@dataclass
class SimulationResult:
    """Results from a single simulation run"""
    config: SimulationConfig
    metrics: Dict[str, float]
    success: bool
    error: Optional[str] = None
    
    @property
    def events(self) -> List[SimulationEvent]:
        """Get events from simulation output"""
        if not self.success:
            return []
            
        events = []
        with open(self.config.output_file) as f:
            for line in f:
                try:
                    events.append(SimulationEvent.from_json(line))
                except (json.JSONDecodeError, KeyError):
                    continue
        return events

@dataclass 
class SweepResults:
    """Results from a parameter sweep"""
    configs: List[SimulationConfig]
    results: List[SimulationResult]
    output_dir: Path
    timestamp: datetime = datetime.now()
    
    def successful_results(self) -> List[SimulationResult]:
        """Get only successful simulation results"""
        return [r for r in self.results if r.success]
    
    def failed_results(self) -> List[SimulationResult]:
        """Get failed simulation results"""
        return [r for r in self.results if not r.success]