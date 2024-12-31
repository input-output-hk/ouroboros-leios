from .base_diffusion import BaseDiffusionAnalyzer
from ..core.events import EventType

class IBDiffusionAnalyzer(BaseDiffusionAnalyzer):
    """Analyzer for input block diffusion through the network"""
    name = "ib_diffusion"
    
    def __init__(self):
        super().__init__(
            block_type="InputBlock",
            gen_param="ib_generation_probability",
            sent_type=EventType.INPUT_BLOCK_SENT,
            received_type=EventType.INPUT_BLOCK_RECEIVED
        )

class EBDiffusionAnalyzer(BaseDiffusionAnalyzer):
    """Analyzer for endorser block diffusion through the network"""
    name = "eb_diffusion"
    
    def __init__(self):
        super().__init__(
            block_type="EndorserBlock",
            gen_param="eb_generation_probability",
            sent_type=EventType.ENDORSER_BLOCK_SENT,
            received_type=EventType.ENDORSER_BLOCK_RECEIVED
        ) 

class RBDiffusionAnalyzer(BaseDiffusionAnalyzer):
    """Analyzer for ranking block (Praos) diffusion through the network"""
    name = "rb_diffusion"
    
    def __init__(self):
        super().__init__(
            block_type="PraosBlock",
            gen_param="block_generation_probability",
            sent_type=EventType.PRAOS_BLOCK_SENT,
            received_type=EventType.PRAOS_BLOCK_RECEIVED
        )

class VoteDiffusionAnalyzer(BaseDiffusionAnalyzer):
    """Analyzer for vote diffusion through the network"""
    name = "vote_diffusion"
    
    def __init__(self):
        super().__init__(
            block_type="Votes",
            gen_param="vote_probability",
            sent_type=EventType.VOTES_SENT,
            received_type=EventType.VOTES_RECEIVED
        )