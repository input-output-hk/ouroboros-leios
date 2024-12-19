from dataclasses import dataclass
from typing import List, Dict, Tuple, Optional

@dataclass
class Node:
    """Node in the network topology"""
    id: int
    stake: int
    location: Tuple[float, float]
    
    @property
    def is_producer(self) -> bool:
        """Node is a producer if it has stake"""
        return self.stake > 0

@dataclass
class Link:
    """Network link between nodes"""
    nodes: Tuple[int, int]
    latency_ms: Optional[int] = None

@dataclass
class Topology:
    """Network topology representation"""
    nodes: List[Node]
    links: List[Link]
    total_stake: int

    @classmethod
    def from_config(cls, config: Dict) -> 'Topology':
        """Create topology from config dictionary"""
        nodes = []
        total_stake = 0
        
        for i, node_config in enumerate(config.get("nodes", [])):
            stake = node_config.get("stake", 0)
            location = tuple(node_config.get("location", [0, 0]))
            nodes.append(Node(id=i, stake=stake, location=location))
            total_stake += stake

        links = [
            Link(
                nodes=tuple(link["nodes"]),
                latency_ms=link.get("latency_ms")
            )
            for link in config.get("links", [])
        ]

        return cls(nodes=nodes, links=links, total_stake=total_stake)

    def get_stake_fraction(self, node_id: int) -> float:
        """Get stake fraction for a node"""
        for node in self.nodes:
            if node.id == node_id:
                return node.stake / self.total_stake if self.total_stake > 0 else 0
        return 0.0 

    @property
    def stats(self) -> dict:
        """Get topology statistics"""
        nodes = self.nodes
        
        # Count node types based on stake
        producers = sum(1 for n in nodes if n.is_producer)
        relays = len(nodes) - producers
        
        # Calculate stake in ADA (1 ADA = 1_000_000 lovelace)
        total_stake_ada = self.total_stake / 1_000_000
        
        return {
            "total_nodes": len(nodes),
            "relays": relays,
            "producers": producers,
            "total_stake_ada": total_stake_ada
        } 