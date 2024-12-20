from .diffusion import BaseDiffusionAnalyzer

class IBDiffusionAnalyzer(BaseDiffusionAnalyzer):
    """Analyzer for input block diffusion through the network"""
    
    name = "ib_diffusion"
    
    def __init__(self):
        super().__init__(
            block_type="InputBlock",
            gen_param="ib_generation_probability"
        )