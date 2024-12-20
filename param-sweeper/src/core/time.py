from dataclasses import dataclass
from typing import Union

@dataclass
class VirtualTime:
    """Represents simulation virtual time in nanoseconds"""
    nanoseconds: int
    
    def __init__(self, time: Union[int, float]):
        """Initialize from nanoseconds (int) or seconds (float)"""
        if isinstance(time, float):
            self.nanoseconds = int(time * 1_000_000_000)
        else:
            self.nanoseconds = time
    
    def as_seconds(self) -> float:
        """Convert to seconds"""
        return self.nanoseconds / 1_000_000_000
    
    def __lt__(self, other: 'VirtualTime') -> bool:
        return self.nanoseconds < other.nanoseconds
    
    def __gt__(self, other: 'VirtualTime') -> bool:
        return self.nanoseconds > other.nanoseconds
    
    def __eq__(self, other: 'VirtualTime') -> bool:
        return self.nanoseconds == other.nanoseconds
    
    def __add__(self, other: 'VirtualTime') -> 'VirtualTime':
        return VirtualTime(self.nanoseconds + other.nanoseconds)
    
    def __sub__(self, other: 'VirtualTime') -> 'VirtualTime':
        return VirtualTime(self.nanoseconds - other.nanoseconds)