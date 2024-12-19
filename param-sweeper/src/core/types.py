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
    
    @property
    def output_file(self) -> Path:
        """Path to simulation output file"""
        return self.sim_dir / f"sim_{self.iteration:04d}.jsonl"
    
    @property
    def config_file(self) -> Path:
        """Path to simulation config file"""
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