"""
Fully-hedging fetch scheduler — extreme baseline for comparison.

Rule: every time we learn that a (manifest, peer-offer) pair is
available for a payload, immediately request every chunk we don't
already have from that peer — regardless of whether the same chunk is
already in flight with other peers. Unbounded duplication. When the
chunk lands from one peer, cancel the redundant in-flight requests on
all others. No probing, no pipeline management, no stall detection.
The counter-extreme is OnePeerScheduler.

Re-exports the Event and Action classes from FetchScheduler so the C
bridge can resolve them via the same attribute lookups.
"""

import os
import random
from dataclasses import dataclass, field

from FetchScheduler import (
    PeerHint, OfferReceived, ManifestReceived, ChunkDelivered,
    CancelConfirmed, BdpEstimated, TimerFired, TcpInfo,
    AssignChunk, CancelChunk, SetTimer, StartProbe, AbortProbe,
    decide_chunks, PayloadState,
)

# Per-peer deterministic permutation of the chunk request order. Staggers
# which chunk each peer transmits first, so that first-arrivals cover
# more of the payload and later-arriving duplicates get cancelled sooner.
# Set FULLHEDGE_SHUFFLE=0 to disable. Default (unset) is enabled.
_shuffle = os.environ.get("FULLHEDGE_SHUFFLE", "1")
if _shuffle not in ("0", "1"):
    raise ValueError(
        "FULLHEDGE_SHUFFLE must be '0' or '1' (or unset); got %r" % _shuffle)
SHUFFLE = (_shuffle == "1")


@dataclass
class PeerState:
    next_seqno: int = 0
    seqno_to_chunk: dict = field(default_factory=dict)    # seqno -> (hash, chunk_id)


@dataclass
class PayloadTracking:
    payload: 'PayloadState'
    delivered: set = field(default_factory=set)           # chunk_ids already received
    pending: dict = field(default_factory=dict)           # chunk_id -> list[(peer_id, seqno)]


@dataclass
class SchedulerState:
    tracked: dict = field(default_factory=dict)     # hash -> PayloadTracking
    peers: dict = field(default_factory=dict)       # peer_id -> PeerState
    offered: dict = field(default_factory=dict)     # hash -> set(peer_id)


def init_state(hedge_threshold_bytes: int) -> SchedulerState:
    return SchedulerState()


def _request_missing(state, pid, tracking):
    """Issue AssignChunk for every chunk we haven't received yet, in a
    per-peer deterministic permutation so peers stagger which chunk they
    transmit first."""
    peer = state.peers.setdefault(pid, PeerState())
    chunks = list(tracking.payload.chunks)
    if SHUFFLE:
        seed = pid.to_bytes(4, 'big') + tracking.payload.payload_hash
        random.Random(seed).shuffle(chunks)
    actions = []
    for chunk in chunks:
        if chunk.chunk_id in tracking.delivered: continue
        seqno = peer.next_seqno
        peer.next_seqno += 1
        peer.seqno_to_chunk[seqno] = (tracking.payload.payload_hash, chunk.chunk_id)
        tracking.pending.setdefault(chunk.chunk_id, []).append((pid, seqno))
        actions.append(AssignChunk(
            peer_id=pid,
            payload_hash=tracking.payload.payload_hash,
            chunk_id=chunk.chunk_id,
            seqno=seqno,
            component_bitmap=chunk.component_bitmap,
        ))
    return actions


def step(state, event):
    if isinstance(event, OfferReceived):
        offerers = state.offered.setdefault(event.payload_hash, set())
        if event.peer_id in offerers:
            return []
        offerers.add(event.peer_id)
        tracking = state.tracked.get(event.payload_hash)
        if tracking is not None:
            return _request_missing(state, event.peer_id, tracking)
        return []

    if isinstance(event, ManifestReceived):
        scratch = PayloadState(payload_hash=event.payload_hash,
                               chunks=[], remaining_bytes=0)
        chunks = decide_chunks(scratch, event.component_sizes)
        payl = PayloadState(
            payload_hash=event.payload_hash,
            chunks=chunks,
            remaining_bytes=sum(c.size for c in chunks),
        )
        tracking = PayloadTracking(payload=payl)
        state.tracked[event.payload_hash] = tracking
        actions = []
        for pid in state.offered.get(event.payload_hash, set()):
            actions += _request_missing(state, pid, tracking)
        return actions

    if isinstance(event, ChunkDelivered):
        peer = state.peers[event.peer_id]
        payload_hash, chunk_id = peer.seqno_to_chunk.pop(event.seqno)
        tracking = state.tracked[payload_hash]
        if chunk_id in tracking.delivered: return []
        tracking.delivered.add(chunk_id)
        # Cancel the redundant in-flight requests for this chunk on all
        # other peers. Popping pending[chunk_id] ensures we only cancel
        # once even if we later receive late duplicate deliveries.
        actions = []
        for pid, seqno in tracking.pending.pop(chunk_id):
            if pid == event.peer_id: continue
            actions.append(CancelChunk(peer_id=pid, seqno=seqno))
        return actions

    if isinstance(event, CancelConfirmed):
        del state.peers[event.peer_id].seqno_to_chunk[event.seqno]
        return []

    return []
