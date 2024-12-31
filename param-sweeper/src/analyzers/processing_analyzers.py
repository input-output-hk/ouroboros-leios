from .base_processing import BaseProcessingTimeAnalyzer
from ..core.events import EventType

class IBProcessingAnalyzer(BaseProcessingTimeAnalyzer):
    """Analyzer for input block processing times"""
    
    name = "ib_processing"
    
    def __init__(self):
        super().__init__(
            message_type="InputBlock",
            generated_type=EventType.INPUT_BLOCK_GENERATED,
            sent_type=EventType.INPUT_BLOCK_SENT
        )

class EBProcessingAnalyzer(BaseProcessingTimeAnalyzer):
    """Analyzer for endorser block processing times"""
    
    name = "eb_processing"
    
    def __init__(self):
        super().__init__(
            message_type="EndorserBlock",
            generated_type=EventType.ENDORSER_BLOCK_GENERATED,
            sent_type=EventType.ENDORSER_BLOCK_SENT
        )

class RBProcessingAnalyzer(BaseProcessingTimeAnalyzer):
    """Analyzer for ranking block (Praos) processing times"""
    
    name = "rb_processing"
    
    def __init__(self):
        super().__init__(
            message_type="PraosBlock",
            generated_type=EventType.PRAOS_BLOCK_GENERATED,
            sent_type=EventType.PRAOS_BLOCK_SENT
        )

class VoteProcessingAnalyzer(BaseProcessingTimeAnalyzer):
    """Analyzer for vote processing times"""
    
    name = "vote_processing"
    
    def __init__(self):
        super().__init__(
            message_type="Votes",
            generated_type=EventType.VOTES_GENERATED,
            sent_type=EventType.VOTES_SENT
        ) 