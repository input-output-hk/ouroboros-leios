from .diffusion import BaseDiffusionAnalyzer

class EBDiffusionAnalyzer(BaseDiffusionAnalyzer):
    """Analyzer for endorser block diffusion through the network"""
    
    name = "eb_diffusion"
    
    def __init__(self):
        super().__init__(
            block_type="EndorserBlock",
            gen_param="eb_generation_probability"
        ) 