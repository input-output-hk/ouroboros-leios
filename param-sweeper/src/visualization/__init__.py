"""
Visualization components for simulation results.
"""

from .base import PlotVisualization
from .plots.ib_diffusion_plots import IBDiffusionPlot

__all__ = [
    'PlotVisualization',
    'IBDiffusionPlot',
]
