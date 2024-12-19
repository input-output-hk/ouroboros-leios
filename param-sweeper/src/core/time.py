from dataclasses import dataclass

@dataclass
class VirtualTime:
    """Represents simulation virtual time with microsecond precision"""
    micros: int
    time_scale: float = 1.0
    
    @property
    def seconds(self) -> float:
        """Convert to seconds for readability, applying time scale"""
        return (self.micros * self.time_scale) / 1_000_000
    
    def __sub__(self, other: 'VirtualTime') -> 'VirtualTime':
        """Calculate time difference"""
        if self.time_scale != other.time_scale:
            raise ValueError("Cannot subtract times with different scale factors")
        return VirtualTime(self.micros - other.micros, self.time_scale)
    
    def __lt__(self, other: 'VirtualTime') -> bool:
        """Compare times"""
        if self.time_scale != other.time_scale:
            raise ValueError("Cannot compare times with different scale factors")
        return self.micros < other.micros 