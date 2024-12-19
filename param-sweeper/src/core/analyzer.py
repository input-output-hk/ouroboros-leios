from abc import ABC, abstractmethod
from typing import Dict, List
from .types import SimulationResult, SweepResults

class SimulationAnalyzer(ABC):
    """Base class for simulation analysis modules"""
    
    @property
    @abstractmethod
    def name(self) -> str:
        """Name of the analyzer (used as prefix for metrics)"""
        pass
    
    @abstractmethod
    def analyze(self, result: SimulationResult) -> Dict[str, float]:
        """Analyze a single simulation result and return metrics"""
        pass
    
    def visualize(self, results: SweepResults) -> None:
        """Generate visualizations from sweep results
        
        Optional method that analyzers can implement to generate plots
        or other visualizations from the sweep results.
        """
        pass