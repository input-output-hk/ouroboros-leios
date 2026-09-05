"""
One-peer fetch scheduler — extreme baseline for comparison.

Rule: as soon as we have both the manifest and at least one offer for a
payload, request every chunk from the *first* offering peer only. No
hedging, no probing, no pipeline depth management, no stall detection,
no rebalance. The counter-extreme is FullHedgeScheduler.

Re-exports the Event and Action classes from FetchScheduler so the C
bridge can resolve them via the same attribute lookups.
"""

from dataclasses import dataclass, field

from FetchScheduler import (
    PeerHint, OfferReceived, ManifestReceived, ChunkDelivered,
    CancelConfirmed, BdpEstimated, TimerFired, TcpInfo,
    AssignChunk, CancelChunk, SetTimer, StartProbe, AbortProbe,
    decide_chunks, PayloadState,
)


@dataclass
class PeerState:
    next_seqno: int = 0


@dataclass
class SchedulerState:
    payloads: dict = field(default_factory=dict)       # hash -> PayloadState
    peers: dict = field(default_factory=dict)          # peer_id -> PeerState
    assigned_to: dict = field(default_factory=dict)    # hash -> peer_id


def init_state(hedge_threshold_bytes: int) -> SchedulerState:
    return SchedulerState()


def _get_or_make_payload(state, payload_hash):
    payl = state.payloads.get(payload_hash)
    if payl is None:
        payl = PayloadState(payload_hash=payload_hash, chunks=[], remaining_bytes=0)
        state.payloads[payload_hash] = payl
    return payl


def _assign_all(state, pid, payl):
    peer = state.peers.setdefault(pid, PeerState())
    actions = []
    for chunk in payl.chunks:
        seqno = peer.next_seqno
        peer.next_seqno += 1
        actions.append(AssignChunk(
            peer_id=pid,
            payload_hash=payl.payload_hash,
            chunk_id=chunk.chunk_id,
            seqno=seqno,
            component_bitmap=chunk.component_bitmap,
        ))
    return actions


def step(state, event):
    if isinstance(event, OfferReceived):
        payl = _get_or_make_payload(state, event.payload_hash)
        payl.peers_offered.add(event.peer_id)
        if payl.chunks and event.payload_hash not in state.assigned_to:
            state.assigned_to[event.payload_hash] = event.peer_id
            return _assign_all(state, event.peer_id, payl)
        return []

    if isinstance(event, ManifestReceived):
        payl = _get_or_make_payload(state, event.payload_hash)
        payl.chunks = decide_chunks(payl, event.component_sizes)
        payl.remaining_bytes = sum(c.size for c in payl.chunks)
        if payl.peers_offered and event.payload_hash not in state.assigned_to:
            pid = next(iter(payl.peers_offered))
            state.assigned_to[event.payload_hash] = pid
            return _assign_all(state, pid, payl)
        return []

    return []
