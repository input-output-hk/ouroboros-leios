from abc import ABC, abstractmethod
from pathlib import Path
from ..core.types import SweepResults

class PlotVisualization(ABC):
    """Base class for plot-based visualizations"""
    
    @property
    @abstractmethod
    def name(self) -> str:
        """Name used for plot files"""
        pass
    
    @abstractmethod
    def generate(self, results: SweepResults, output_dir: Path) -> None:
        """Generate visualization from sweep results"""
        pass
    
    def save_plot(self, plot, output_dir: Path, suffix: str = "") -> None:
        """Save plot with standard naming"""
        # Create plots directory if it doesn't exist
        plots_dir = output_dir / "plots"
        plots_dir.mkdir(parents=True, exist_ok=True)
        
        # Save plot
        filename = f"{self.name}{suffix}.png"
        plot.savefig(plots_dir / filename, bbox_inches='tight')
        plot.close() 