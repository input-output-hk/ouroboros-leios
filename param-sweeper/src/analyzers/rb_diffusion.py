from .diffusion import BaseDiffusionAnalyzer

class RBDiffusionAnalyzer(BaseDiffusionAnalyzer):
    """Analyzer for ranking block (Praos) diffusion through the network"""
    
    name = "rb_diffusion"
    
    def __init__(self):
        super().__init__(
            block_type="PraosBlock",  # Matches event types in events.py: PraosBlockGenerated, PraosBlockSent, PraosBlockReceived
            gen_param="block_generation_probability"  # This is the Praos block generation probability
        ) 