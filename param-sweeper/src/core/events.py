from enum import Enum
from typing import Dict, Any, Iterator, Optional
from dataclasses import dataclass
from .types import SimulationEvent

class EventType(Enum):
    # Core events
    SLOT = "Slot"
    
    # Transaction events
    TRANSACTION_GENERATED = "TransactionGenerated"
    TRANSACTION_SENT = "TransactionSent"
    TRANSACTION_RECEIVED = "TransactionReceived"
    
    # Input Block events
    INPUT_BLOCK_GENERATED = "InputBlockGenerated"
    INPUT_BLOCK_SENT = "InputBlockSent"
    INPUT_BLOCK_RECEIVED = "InputBlockReceived"
    
    # Endorser Block events
    ENDORSER_BLOCK_GENERATED = "EndorserBlockGenerated"
    ENDORSER_BLOCK_SENT = "EndorserBlockSent"
    ENDORSER_BLOCK_RECEIVED = "EndorserBlockReceived"
    
    # Vote events
    VOTES_GENERATED = "VotesGenerated"
    VOTES_SENT = "VotesSent"
    VOTES_RECEIVED = "VotesReceived"
    NO_VOTE_GENERATED = "NoVote"
    
    # Praos Block events
    PRAOS_BLOCK_GENERATED = "PraosBlockGenerated"
    PRAOS_BLOCK_SENT = "PraosBlockSent"
    PRAOS_BLOCK_RECEIVED = "PraosBlockReceived"

@dataclass
class EventFilter:
    """Filter for event iteration"""
    type: Optional[EventType] = None
    start_time: Optional[float] = None
    end_time: Optional[float] = None
    
    def matches(self, event: SimulationEvent) -> bool:
        """Check if event matches filter"""
        if self.type and event.type != self.type.value:
            return False
        if self.start_time and event.time < self.start_time:
            return False
        if self.end_time and event.time > self.end_time:
            return False
        return True

class EventStream:
    """Utility class for working with simulation events"""
    
    def __init__(self, events: list[SimulationEvent]):
        self.events = events
    
    def filter(self, 
               type: Optional[EventType] = None,
               start_time: Optional[float] = None,
               end_time: Optional[float] = None) -> 'EventStream':
        """Create filtered view of events"""
        filter = EventFilter(type, start_time, end_time)
        return EventStream([e for e in self.events if filter.matches(e)])
    
    def by_type(self, type: EventType) -> 'EventStream':
        """Filter events by type"""
        return self.filter(type=type)
    
    def in_time_range(self, start: float, end: float) -> 'EventStream':
        """Filter events by time range"""
        return self.filter(start_time=start, end_time=end)
    
    def count(self) -> int:
        """Count events"""
        return len(self.events)
    
    def __iter__(self) -> Iterator[SimulationEvent]:
        return iter(self.events) 