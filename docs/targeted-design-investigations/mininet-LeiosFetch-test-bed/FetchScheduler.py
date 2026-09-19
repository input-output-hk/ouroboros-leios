"""
Fetch scheduling policy — pure state machine.

(state, event) → (state, [actions])

No I/O, no side effects. The C node drives this by feeding events
and executing the returned actions.

Multiple payloads may be in flight concurrently. Peers are shared
across payloads (same TCP connections), so scheduling decisions
must account for cross-payload bandwidth sharing.
"""

from dataclasses import dataclass, field
from typing import Optional, Union
import math
import sys

TRACE = True

def trace(msg):
    if TRACE:
        print(msg, file=sys.stderr)


@dataclass(frozen=True)
class Probationary:
    """Unproven peer, or recovering from stall."""
    stall_count: int = 0  # 0 for fresh peers; preserved across stall/recovery cycles

@dataclass(frozen=True)
class Probing:
    """Peer is being probed to discover its BDP. Pipeline depth during
    this phase is probe_size_bytes (much larger than BDP) so we keep the
    peer's TCP non-app-limited long enough for cwnd to reach steady state.
    Transitions to Normal on BdpEstimated event."""
    probe_size_bytes: int

@dataclass(frozen=True)
class Normal:
    """Proven peer, delivering reliably."""
    pass

@dataclass(frozen=True)
class Snubbing:
    """Missed deadline, we snub them for an exponential backoff."""
    stall_count: int

PeerStatus = Union[Probationary, Probing, Normal, Snubbing]


# ---------------------------------------------------------------------------
# Constants
# ---------------------------------------------------------------------------

TARGET_CHUNK_BYTES = 65536
PROBATIONARY_CHUNKS = 2
PROBE_SIZE_BYTES = 2 * 1024 * 1024  # burst size for BDP probe (see DESIGN.md)
PROBE_MIN_WORK_BYTES = PROBE_SIZE_BYTES  # don't probe if total pending work is below this
STALL_TIMEOUT_MULTIPLIER = 5  # snub if no delivery within this × expected chunk time
PIPELINE_DEPTH_BDP_MULTIPLIER = 2.5  # how many BDPs of chunks to keep in flight
TIMER_GRANULARITY_MS = 50     # debounce: round timer delays up to this granularity
REBALANCE_INTERVAL_MS = 100   # periodic rebalance check
REBALANCE_MIN_SPEEDUP = 2.0     # only steal if donor_est / recipient_est >= this
REBALANCE_MIN_SAVING_S = 0.05  # ...and donor_est - recipient_est >= this (seconds)
SNUBBING_BASE_MS = 200        # first recovery attempt after this long
SNUBBING_MAX_MS = 30000       # cap on exponential backoff



# ---------------------------------------------------------------------------
# Types
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class TcpInfo:
    """Snapshot of kernel TCP_INFO for a socket (RTT only on the receiver
    side; see DESIGN.md for why tcpi_snd_cwnd is not useful here)."""
    rtt_us: int          # smoothed RTT (microseconds)


@dataclass
class PeerState:
    """Per-peer tracking, shared across all payloads on this connection."""
    tcp_info: Optional[TcpInfo] = None
    status: PeerStatus = field(default_factory=Probationary)
    # In-flight chunks in chronological assignment order, across all payloads.
    inflight: list = field(default_factory=list)  # [ChunkState]
    # Subsequence of inflight containing only chunks still assigned to this
    # peer (i.e., not yet cancelled). Cancelled chunks remain in `inflight`
    # for capacity accounting but drop out of `assigned_inflight`.
    assigned_inflight: list = field(default_factory=list)  # [ChunkState]
    # Parallel to inflight (same length, same order): the precomputed
    # stall deadline (wall-clock seconds) for each pending-reply chunk.
    # Set at do_assign time from the amount of pending-reply work
    # already ahead of this chunk in the peer's queue — further-back
    # chunks have later deadlines, reflecting that they legitimately
    # have more to wait through. Preserved across do_cancel (either
    # reply type resolves the deadline). Popped by release_inflight.
    deadlines: list = field(default_factory=list)  # [float], parallel to inflight
    inflight_bytes: int = 0  # sum of sizes; kept in sync by do_assign/do_unassign
    next_seqno: int = 0  # monotonic per-peer, for cancel targeting
    seqno_to_chunk: dict = field(default_factory=dict)  # seqno -> ChunkState
    # Measured BDP, set by BdpEstimated event after a successful probe.
    # 0 means unknown — no probe has plateaued yet.
    bdp_bytes: int = 0
    min_rtt_seen_us: int = 0   # low-water mark for RTT; 0 means no data yet


@dataclass(frozen=True)
class AssignmentInfo:
    """Per-(chunk, peer) metadata, set at assignment time."""
    when: float
    seqno: int


@dataclass
class ChunkState:
    """Per-chunk tracking within a payload."""
    chunk_id: int
    size: int
    component_bitmap: bytes = b''      # bitmask of which components this chunk covers
    payload: 'PayloadState' = None     # back-pointer
    deliverer: Optional[int] = None    # peer ID; None means not yet delivered
    assignments: dict = field(default_factory=dict)  # peer_id -> AssignmentInfo


@dataclass
class PayloadState:
    """Per-payload fetch state."""
    payload_hash: bytes
    chunks: list       # [ChunkState], empty until manifest arrives
    remaining_bytes: int
    peers_offered: set = field(default_factory=set)  # peer IDs that have offered


@dataclass
class SchedulerState:
    """Complete scheduler state across all concurrent payload fetches."""
    payloads: dict     # payload_hash -> PayloadState
    peers: dict        # peer_id -> PeerState
    hedge_threshold_bytes: int  # operator parameter
    time: float = 0.0
    active_stall_timers: set = field(default_factory=set)  # peer_ids with an active timer
    rebalance_timer_active: bool = False
    completed_payloads: set = field(default_factory=set)  # payload hashes we finished
    tcp_info_generation: int = 0       # incremented on any tcp_info update
    last_rebalance_generation: int = 0 # tcp_info_generation at last rebalance


# ---------------------------------------------------------------------------
# Events (inputs from the C node)
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class PeerHint:
    """Pre-populate a peer with a synthetic TcpInfo estimate (e.g. from topology config).
    Resets the peer's status to Normal."""
    peer_id: int
    tcp_info: TcpInfo
    time: float


@dataclass(frozen=True)
class OfferReceived:
    peer_id: int
    payload_hash: bytes
    tcp_info: Optional[TcpInfo]
    time: float


@dataclass(frozen=True)
class ManifestReceived:
    """The manifest for a new payload has arrived and been parsed."""
    payload_hash: bytes
    component_sizes: tuple  # immutable sequence of int
    time: float


@dataclass(frozen=True)
class ChunkDelivered:
    peer_id: int
    seqno: int
    tcp_info: TcpInfo
    time: float


@dataclass(frozen=True)
class CancelConfirmed:
    """The peer confirmed it cancelled the request (sent MSG_CANCELED_RESPONSE)."""
    peer_id: int
    seqno: int
    tcp_info: TcpInfo
    time: float


@dataclass(frozen=True)
class BdpEstimated:
    """The C-side bdp_estimator has transitioned to KNOWN for this peer —
    plateau detected during a probe burst. The scheduler should transition
    the peer to Normal, record the BDP, and cancel excess in-flight chunks."""
    peer_id: int
    bdp_bytes: int
    rtmin_us: int
    time: float


@dataclass(frozen=True)
class TimerFired:
    """A timer has fired. peer_id is set for stall-check timers, None for rebalance."""
    peer_id: Optional[int]
    peer_tcp_infos: dict  # peer_id -> TcpInfo (fresh snapshot at fire time)
    time: float


Event = Union[PeerHint, OfferReceived, ManifestReceived, ChunkDelivered, CancelConfirmed, BdpEstimated, TimerFired]


# ---------------------------------------------------------------------------
# Actions (outputs to the C node)
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class AssignChunk:
    peer_id: int
    payload_hash: bytes
    chunk_id: int
    seqno: int
    component_bitmap: bytes


@dataclass(frozen=True)
class CancelChunk:
    peer_id: int
    seqno: int


@dataclass(frozen=True)
class SetTimer:
    """Request the C node to fire a TimerFired after delay_ms.
    peer_id is set for stall-check timers, None for rebalance."""
    peer_id: Optional[int]
    delay_ms: int


@dataclass(frozen=True)
class StartProbe:
    """Tell the C node to put this peer's bdp_estimator into Probing state.
    The scheduler will follow up with enough AssignChunks to fill the probe
    burst, keeping the peer non-app-limited long enough for a plateau to
    emerge."""
    peer_id: int


@dataclass(frozen=True)
class AbortProbe:
    """Tell the C node that an in-flight probe is being abandoned (e.g. the
    peer just got snubbed). Reverts PROBING → UNKNOWN without doubling the
    probe size, so the next probe attempt reuses the same size."""
    peer_id: int


Action = Union[AssignChunk, CancelChunk, SetTimer, StartProbe, AbortProbe]


# ---------------------------------------------------------------------------
# Initialization
# ---------------------------------------------------------------------------

def make_component_bitmap(comp_ids: list, num_components: int) -> bytes:
    """Build a packed bitmap with one bit per component."""
    num_bytes = (num_components + 7) // 8
    bm = bytearray(num_bytes)
    for cid in comp_ids:
        bm[cid // 8] |= 1 << (cid % 8)
    return bytes(bm)


def decide_chunks(payl: 'PayloadState', component_sizes) -> list:
    """Partition components into chunks of roughly TARGET_CHUNK_BYTES."""
    num_components = len(component_sizes)
    chunks = []
    current_ids = []
    current_size = 0
    for comp_id, size in enumerate(component_sizes):
        current_ids.append(comp_id)
        current_size += size
        if current_size > TARGET_CHUNK_BYTES:
            chunks.append(ChunkState(
                chunk_id=len(chunks),
                size=current_size,
                component_bitmap=make_component_bitmap(current_ids, num_components),
                payload=payl,
            ))
            current_ids = []
            current_size = 0
    if current_size > 0:
        chunks.append(ChunkState(
            chunk_id=len(chunks),
            size=current_size,
            component_bitmap=make_component_bitmap(current_ids, num_components),
            payload=payl,
        ))
    return chunks


def init_state(hedge_threshold_bytes: int) -> SchedulerState:
    """Create initial scheduler state (no payloads yet)."""
    return SchedulerState(
        payloads={},
        peers={},
        hedge_threshold_bytes=hedge_threshold_bytes,
    )


def get_or_create_payload(state: SchedulerState, payload_hash: bytes) -> Optional[PayloadState]:
    """Get existing PayloadState or create an empty one (pre-manifest).
    Returns None if the payload was already completed."""
    if payload_hash in state.completed_payloads:
        return None
    payl = state.payloads.get(payload_hash)
    if payl is None:
        payl = PayloadState(
            payload_hash=payload_hash, chunks=[], remaining_bytes=0,
        )
        state.payloads[payload_hash] = payl
    return payl


def update_peer_tcp_info(state: SchedulerState, peer: PeerState, tcpi: TcpInfo):
    """Update a peer's tcp_info and maintain the RTmin low-water mark."""
    peer.tcp_info = tcpi
    if tcpi.rtt_us > 0 and (peer.min_rtt_seen_us == 0 or tcpi.rtt_us < peer.min_rtt_seen_us):
        peer.min_rtt_seen_us = tcpi.rtt_us
    state.tcp_info_generation += 1


# ---------------------------------------------------------------------------
# Estimation
# ---------------------------------------------------------------------------

def pipeline_depth_target(peer: PeerState) -> int:
    """How many bytes should be in flight to this peer (across all payloads).
    Chosen by peer status:
      Probationary/Snubbing: PROBATIONARY_CHUNKS chunks (conservative).
      Probing: probe_size_bytes — deliberately large to keep peer non-app-
        limited long enough for TCP slow-start to reach steady-state cwnd,
        so a plateau in arrival rate can be observed.
      Normal: measured BDP, once a probe has plateaued; PROBATIONARY floor
        while bdp_bytes is still 0.
    See DESIGN.md "BDP estimation" for the full rationale."""
    if isinstance(peer.status, Probing):
        return peer.status.probe_size_bytes
    if isinstance(peer.status, (Probationary, Snubbing)):
        return PROBATIONARY_CHUNKS * TARGET_CHUNK_BYTES
    # Normal: floor at 2 chunks so that when BDP happens to be just under
    # chunk size (e.g. 59 KB on a 1 Gbps / 1 ms link), we don't collapse
    # to a single-chunk pipeline and strand the peer one-chunk-at-a-time.
    if peer.bdp_bytes > 0:
        return max(PROBATIONARY_CHUNKS * TARGET_CHUNK_BYTES,
                   int(PIPELINE_DEPTH_BDP_MULTIPLIER * peer.bdp_bytes))
    return PROBATIONARY_CHUNKS * TARGET_CHUNK_BYTES


def peer_capacity(peer: PeerState) -> int:
    """How many more bytes this peer can accept across all payloads."""
    return max(0, pipeline_depth_target(peer) - peer.inflight_bytes)


def estimated_throughput(peer: PeerState) -> float:
    """Peer's steady-state throughput in bytes/sec: BDP / RTmin once known.
    0 while a peer has no BDP estimate yet."""
    if peer.bdp_bytes > 0 and peer.min_rtt_seen_us > 0:
        return peer.bdp_bytes / (peer.min_rtt_seen_us / 1e6)
    return 0.0


def estimated_time_for_new_chunk(peer: PeerState, chunk_size: int) -> float:
    """Estimate delivery time if a new chunk of given size were appended to
    this peer's queue (i.e., it's not yet in inflight)."""
    throughput = estimated_throughput(peer)
    if throughput == 0 or peer.min_rtt_seen_us == 0:
        return float('inf')
    return peer.min_rtt_seen_us / 1e6 + (peer.inflight_bytes + chunk_size) / throughput


# ---------------------------------------------------------------------------
# Chunk assignment and cancellation
# ---------------------------------------------------------------------------

def do_assign(state: SchedulerState,
              peer_id: int, chunk: ChunkState) -> AssignChunk:
    """Record a chunk assignment and return the action."""
    peer = state.peers[peer_id]
    seqno = peer.next_seqno
    peer.next_seqno += 1
    trace("SCHED assign peer=%d seqno=%d chunk=%d payload=%s" % (
        peer_id, seqno, chunk.chunk_id, chunk.payload.payload_hash[:4].hex()))
    chunk.assignments[peer_id] = AssignmentInfo(
        when=state.time, seqno=seqno)
    # Stall deadline is computed now, using the peer's pending work at
    # this moment — including capacity held by already-cancelled
    # chunks, which either deliver anyway (as MSG_RESPONSE) or confirm
    # their cancellation (as MSG_CANCELED_RESPONSE), and in either
    # case still flow down the peer's reply pipe before our new chunk.
    # estimated_time_for_new_chunk uses peer.inflight_bytes, which is
    # pre-append here — so it captures exactly that. If throughput
    # isn't known yet (Probing pre-BDP), fall back to a generous
    # 5 s grace so probe-era assignments don't false-stall.
    work_s = STALL_TIMEOUT_MULTIPLIER * estimated_time_for_new_chunk(peer, chunk.size)
    if not math.isfinite(work_s):
        work_s = 5.0
    peer.inflight.append(chunk)
    peer.deadlines.append(state.time + work_s)
    peer.assigned_inflight.append(chunk)
    peer.inflight_bytes += chunk.size
    peer.seqno_to_chunk[seqno] = chunk
    return AssignChunk(peer_id, chunk.payload.payload_hash, chunk.chunk_id,
                       seqno, chunk.component_bitmap)


def maybe_promote_snubbing(state: SchedulerState, peer_id: int) -> bool:
    """Promote Snubbing -> Probationary once the recovery timer has fired
    (pid no longer in active_stall_timers) and inflight has drained."""
    peer = state.peers[peer_id]
    if (isinstance(peer.status, Snubbing)
            and not peer.inflight
            and peer_id not in state.active_stall_timers):
        peer.status = Probationary(stall_count=peer.status.stall_count)
        return True
    return False


def release_inflight(state: SchedulerState, peer_id: int, chunk: ChunkState):
    """Remove a chunk from a peer's inflight queue, freeing capacity.
    The chunk must already be out of assigned_inflight (do_cancel or
    do_unassign is responsible for that).

    Note: the chunk is *usually* the head of peer.inflight — normal
    MSG_RESPONSE replies arrive in FIFO order — but not always. The
    protocol sends MSG_CANCELED_RESPONSE on a high-priority queue so
    cancellations free capacity promptly, which means cancel-confirms
    can leap-frog regular responses queued ahead of them. So
    release_inflight has to find the chunk anywhere in the list."""
    peer = state.peers[peer_id]
    idx = peer.inflight.index(chunk)
    peer.inflight.pop(idx)
    peer.deadlines.pop(idx)
    peer.inflight_bytes -= chunk.size
    if not peer.inflight:
        state.active_stall_timers.discard(peer_id)


def do_unassign(state: SchedulerState,
                peer_id: int, chunk: ChunkState) -> int:
    """Fully remove a chunk assignment (delivered successfully). Returns the seqno."""
    seqno = chunk.assignments[peer_id].seqno
    del chunk.assignments[peer_id]
    state.peers[peer_id].assigned_inflight.remove(chunk)
    release_inflight(state, peer_id, chunk)
    return seqno


def do_cancel(state: SchedulerState,
              peer_id: int, chunk: ChunkState) -> CancelChunk:
    """Cancel a chunk assignment. Removes from assignments and from
    assigned_inflight, but keeps the chunk in peer.inflight (capacity
    stays reserved until the peer confirms via CancelConfirmed or
    delivers anyway)."""
    seqno = chunk.assignments[peer_id].seqno
    del chunk.assignments[peer_id]
    state.peers[peer_id].assigned_inflight.remove(chunk)
    # Chunk stays in peer.inflight — capacity is not freed until
    # ChunkDelivered or CancelConfirmed for this seqno.
    return CancelChunk(peer_id, seqno)


# ---------------------------------------------------------------------------
# Scheduling logic
# ---------------------------------------------------------------------------

def assign_available(state: SchedulerState, payl: PayloadState) -> list:
    """Assign unassigned chunks to peers with capacity."""
    actions = []
    pool = [c for c in payl.chunks if c.deliverer is None and not c.assignments]
    pool_idx = 0

    eligible = sorted(
        [(pid, peer_capacity(state.peers[pid]))
         for pid in payl.peers_offered
         if not isinstance(state.peers[pid].status, Snubbing)],
        key=lambda x: -x[1],
    )

    for pid, cap in eligible:
        while cap > 0 and pool_idx < len(pool):
            chunk = pool[pool_idx]
            actions.append(do_assign(state, pid, chunk))
            pool_idx += 1
            cap -= chunk.size

    return actions


def rebalance(state: SchedulerState, payloads: list) -> list:
    """Reclaim chunks from slow peers to feed hungry ones, across all payloads.
    Called at most every REBALANCE_INTERVAL_MS, gated by tcp_info_generation.
    Only emits actions if it finds a strictly better assignment, so a
    no-op call (when TCP_INFO changed trivially) costs only CPU, not
    network traffic. An implementation could skip calls when no TCP_INFO
    changed significantly, but defining "significantly" is a judgment
    call best deferred to profiling."""
    actions = []

    hungry = [(pid, peer_capacity(state.peers[pid]))
              for pid in state.peers
              if not isinstance(state.peers[pid].status, Snubbing)
              and peer_capacity(state.peers[pid]) > 0]
    if not hungry:
        return actions

    for hungry_pid, hungry_cap in sorted(hungry, key=lambda x: -x[1]):
        # Collect up to hungry_cap stealable chunks per donor,
        # searching from the back of each queue (later = slower).
        candidates = []  # [(est_time, donor_pid, chunk)]

        for donor_pid, donor in state.peers.items():
            if not donor.inflight:
                continue
            # Don't steal from a peer that's currently being probed —
            # rebalancing the probe's chunks away would sabotage the
            # rate measurement. BBR's Startup phase is equally
            # untouchable by cross-flow interference.
            if isinstance(donor.status, Probing):
                continue
            found_bytes = 0
            for idx in range(len(donor.inflight) - 1, -1, -1):
                if found_bytes >= hungry_cap:
                    break
                chunk = donor.inflight[idx]
                if chunk.deliverer is not None:
                    continue
                if hungry_pid in chunk.assignments:
                    continue
                if hungry_pid not in chunk.payload.peers_offered:
                    continue
                est_time = donor.deadlines[idx] - state.time
                candidates.append((est_time, donor_pid, chunk))
                found_bytes += chunk.size

        # Steal worst-first. Since candidates are sorted by descending
        # est_time and recipient_est grows with each steal, the gap
        # shrinks monotonically — once worthwhileness fails, it fails
        # for all remaining candidates.
        # Sort by est_time only; ChunkState is not orderable, so without
        # an explicit key Python falls through to comparing chunks on
        # ties (e.g. when two donors have est_time=inf).
        candidates.sort(key=lambda t: t[0], reverse=True)
        for est_time, donor_pid, chunk in candidates:
            if hungry_cap <= 0:
                break
            if chunk.deliverer is not None:
                continue
            if donor_pid not in chunk.assignments:
                continue
            recipient_est = STALL_TIMEOUT_MULTIPLIER * estimated_time_for_new_chunk(
                state.peers[hungry_pid], chunk.size)
            if (est_time < REBALANCE_MIN_SPEEDUP * recipient_est
                    or est_time - recipient_est < REBALANCE_MIN_SAVING_S):
                break
            actions.append(do_cancel(state, donor_pid, chunk))
            actions.append(do_assign(state, hungry_pid, chunk))
            hungry_cap -= chunk.size

    return actions


def apply_hedging(state: SchedulerState, payl: PayloadState) -> list:
    """When remaining bytes are below the hedge threshold, assign undelivered
    chunks to additional peers."""
    if payl.remaining_bytes > state.hedge_threshold_bytes:
        return []

    actions = []

    import bisect

    # Precompute per-peer throughput (doesn't change during hedging).
    throughput_cache = {pid: estimated_throughput(state.peers[pid])
                        for pid in payl.peers_offered
                        if isinstance(state.peers[pid].status, Normal)}

    # Build initial sorted list by estimated time: (est, pid).
    # est = (inflight_bytes + TARGET_CHUNK_BYTES) / throughput as a proxy.
    eligible = []
    for pid, throughput in throughput_cache.items():
        if throughput == 0:
            continue
        est = state.peers[pid].inflight_bytes / throughput
        bisect.insort(eligible, (est, pid))

    for chunk in payl.chunks:
        if chunk.deliverer is not None:
            continue
        for est, pid in list(eligible):
            if pid in chunk.assignments:
                continue
            if peer_capacity(state.peers[pid]) < chunk.size:
                continue
            actions.append(do_assign(state, pid, chunk))
            # Re-insert with updated estimate.
            eligible.remove((est, pid))
            throughput = throughput_cache[pid]
            new_est = state.peers[pid].inflight_bytes / throughput
            bisect.insort(eligible, (new_est, pid))
            # Remove peers with no remaining capacity.
            if peer_capacity(state.peers[pid]) <= 0:
                eligible.remove((new_est, pid))

    return actions


def round_up_timer(delay_ms: int) -> int:
    """Round a timer delay up to the nearest TIMER_GRANULARITY_MS."""
    return ((delay_ms + TIMER_GRANULARITY_MS - 1)
            // TIMER_GRANULARITY_MS) * TIMER_GRANULARITY_MS


def ensure_rebalance_timer(state: SchedulerState) -> list:
    """Ensure a periodic rebalance timer is active if any payloads are in flight."""
    if state.rebalance_timer_active or not state.payloads:
        return []
    state.rebalance_timer_active = True
    return [SetTimer(None, REBALANCE_INTERVAL_MS)]


def ensure_stall_timers(state: SchedulerState) -> list:
    """For each peer with in-flight chunks, ensure there's exactly one active
    stall-check timer, targeting the earliest deadline across all payloads.

    Uses peer.inflight (all pending-reply chunks, including cancelled
    ones): we're waiting on a reply to every entry, regardless of
    whether it'll be a MSG_RESPONSE or a MSG_CANCELED_RESPONSE.
    Deadlines were precomputed at assignment time (see do_assign)."""
    actions = []
    for pid, peer in state.peers.items():
        if (pid in state.active_stall_timers
                or isinstance(peer.status, Snubbing)
                or not peer.inflight):
            continue

        earliest_deadline = peer.deadlines[0]
        delay_ms = round_up_timer(max(1, int((earliest_deadline - state.time) * 1000)))

        state.active_stall_timers.add(pid)
        actions.append(SetTimer(pid, delay_ms))
    return actions


def schedule_payloads(state: SchedulerState, payloads) -> list:
    """Schedule a batch of payloads. Hedging runs first across all payloads
    (urgent tail-latency work), then assignment fills remaining capacity.
    Rebalancing is handled separately by the rebalance timer.

    Also decides whether to kick off BDP probes on any offering peer we
    haven't proven yet. Done here (rather than in OfferReceived) because
    MSG_OFFER may arrive before MSG_RESPONSE_MANIFEST and we must defer
    the probe until we have chunks to request anyway."""
    actions = []
    # Candidate peers for probing: those offering at least one payload
    # whose chunks we already know about. Work that a peer hasn't offered
    # can't be requested from them, so it doesn't count toward the probe
    # budget for that peer.
    probable = {}  # pid -> offered_remaining_bytes
    for payl in state.payloads.values():
        for pid in payl.peers_offered:
            probable[pid] = probable.get(pid, 0) + payl.remaining_bytes
    for pid, offered_pending in probable.items():
        if offered_pending < PROBE_MIN_WORK_BYTES: continue
        peer = state.peers.get(pid)
        if peer is None: continue
        if isinstance(peer.status, Probationary):
            peer.status = Probing(probe_size_bytes=PROBE_SIZE_BYTES)
            actions.append(StartProbe(peer_id=pid))
    for payl in payloads:
        actions += apply_hedging(state, payl)
    for payl in payloads:
        actions += assign_available(state, payl)
    return actions


# ---------------------------------------------------------------------------
# State machine transition
# ---------------------------------------------------------------------------

def step(state: SchedulerState, event: Event) -> list:
    """Process one event, mutate state, return actions."""
    actions = []
    state.time = event.time

    if isinstance(event, PeerHint):
        pid = event.peer_id
        if pid not in state.peers:
            state.peers[pid] = PeerState()
        update_peer_tcp_info(state, state.peers[pid], event.tcp_info)
        # Hints are simulation-only; the scheduler must remain correct with
        # no hint delivered. We set the rtt floor (above) but leave status
        # at Probationary so the first real workload triggers a probe.
        trace("SCHED hint peer=%d rtt=%d" % (pid, event.tcp_info.rtt_us))

    elif isinstance(event, ManifestReceived):
        payl = get_or_create_payload(state, event.payload_hash)
        if payl is not None and not payl.chunks:
            payl.chunks = decide_chunks(payl, event.component_sizes)
            payl.remaining_bytes = sum(c.size for c in payl.chunks)
            if payl.peers_offered:
                actions += schedule_payloads(state, [payl])

    elif isinstance(event, OfferReceived):
        pid = event.peer_id
        if pid not in state.peers:
            state.peers[pid] = PeerState()
        peer = state.peers[pid]
        update_peer_tcp_info(state, peer, event.tcp_info)

        payl = get_or_create_payload(state, event.payload_hash)
        if payl is not None:
            payl.peers_offered.add(pid)
            if payl.chunks:
                actions += schedule_payloads(state, [payl])
                trace("SCHED offer peer=%d status=%s depth=%d inflight=%d cap=%d assigns=%d cancels=%d" % (
                    pid, type(peer.status).__name__,
                    pipeline_depth_target(peer), len(peer.inflight),
                    peer_capacity(peer),
                    sum(1 for a in actions if isinstance(a, AssignChunk)),
                    sum(1 for a in actions if isinstance(a, CancelChunk))))

    elif isinstance(event, ChunkDelivered):
        pid = event.peer_id
        peer = state.peers[pid]

        chunk = peer.seqno_to_chunk.pop(event.seqno)

        payl = chunk.payload

        if chunk.deliverer is None:
            chunk.deliverer = pid
            payl.remaining_bytes -= chunk.size

            # Cancel this chunk at all other assigned peers — except
            # ones that are currently probing. Their probe relies on
            # bytes continuing to arrive; cancelling a chunk mid-probe
            # perturbs the rate measurement.
            for other_pid in list(chunk.assignments):
                if other_pid == pid: continue
                if isinstance(state.peers[other_pid].status, Probing):
                    continue
                actions.append(do_cancel(state, other_pid, chunk))

            # Payload completed on this delivery — handle once, here, not
            # on subsequent late deliveries from other peers.
            if payl.remaining_bytes <= 0:
                state.completed_payloads.add(payl.payload_hash)
                del state.payloads[payl.payload_hash]

        # Free inflight capacity. If still assigned, do_unassign handles both
        # assignments and inflight. If already cancelled, only free inflight.
        if pid in chunk.assignments:
            do_unassign(state, pid, chunk)
        elif chunk in peer.inflight:
            release_inflight(state, pid, chunk)

        maybe_promote_snubbing(state, pid)

        update_peer_tcp_info(state, peer, event.tcp_info)
        # Status transitions on delivery:
        #  - Probing: leave it; BdpEstimated owns the transition.
        #  - Snubbing: leave it; recovery timer owns the transition.
        #  - Fresh Probationary (stall_count == 0): the peer has delivered
        #    without having been probed yet — promote to Normal with the
        #    conservative 2-chunk fallback. This is the "not worth probing
        #    right now" path, e.g. when total_pending was below the probe
        #    threshold at schedule_payloads time.
        #  - Probationary after snub recovery (stall_count > 0): keep the
        #    peer probationary so schedule_payloads can re-probe it, rather
        #    than quietly settling at the fallback forever.
        if (isinstance(peer.status, Probationary)
                and peer.status.stall_count == 0):
            peer.status = Normal()

        # Schedule all active payloads — delivery and cancellation free
        # capacity on multiple peers, which is shared across payloads.
        actions += schedule_payloads(state,
            [p for p in state.payloads.values() if p.remaining_bytes > 0])

        trace("SCHED delivery peer=%d seqno=%d status=%s depth=%d inflight=%d cap=%d remaining=%d rtt=%d" % (
            pid, event.seqno, type(peer.status).__name__,
            pipeline_depth_target(peer), len(peer.inflight),
            peer_capacity(peer), payl.remaining_bytes,
            event.tcp_info.rtt_us))

    elif isinstance(event, CancelConfirmed):
        pid = event.peer_id
        peer = state.peers[pid]
        chunk = peer.seqno_to_chunk.pop(event.seqno)
        if chunk in peer.inflight:
            release_inflight(state, pid, chunk)
        maybe_promote_snubbing(state, pid)
        update_peer_tcp_info(state, peer, event.tcp_info)

        actions += schedule_payloads(state,
            [p for p in state.payloads.values() if p.remaining_bytes > 0])

        # TODO we could now move up deadlines for requests that were
        # scheduled after this one
        #
        # Note that the active timer's deadline will never be
        # accelerated.  That would imply that the CancelConfirmed
        # itself was late, so we're already stalled at that point.
        pass

    elif isinstance(event, BdpEstimated):
        # Probe plateau detected on C side. Record BDP, promote peer to
        # Normal, and cancel excess in-flight chunks beyond the BDP target.
        # See DESIGN.md "Cancel-prediction lemma": chunks queued beyond the
        # bytes-on-wire threshold are purgeable; the ones the peer has
        # already started sending will deliver normally and be ignored.
        pid = event.peer_id
        peer = state.peers[pid]
        peer.bdp_bytes = event.bdp_bytes
        if event.rtmin_us > 0 and (peer.min_rtt_seen_us == 0
                                   or event.rtmin_us < peer.min_rtt_seen_us):
            peer.min_rtt_seen_us = event.rtmin_us
        peer.status = Normal()

        # Cancel the deepest-queued excess. Keep enough currently-assigned
        # backlog to match the post-plateau pipeline target; cancel chunks
        # beyond that. do_cancel keeps the chunk in peer.inflight for
        # capacity accounting, so the peer's reported inflight_bytes does
        # not drop immediately — but the chunk is freed from assignments
        # and can be reassigned to a different peer.
        keep_budget = pipeline_depth_target(peer)
        kept_bytes = 0
        to_cancel = []
        for chunk in peer.assigned_inflight:
            if kept_bytes + chunk.size <= keep_budget:
                kept_bytes += chunk.size
            else:
                to_cancel.append(chunk)
        for chunk in to_cancel:
            actions.append(do_cancel(state, pid, chunk))

        # Rescheduling may reassign freed chunks to other peers.
        actions += schedule_payloads(state,
            [p for p in state.payloads.values() if p.remaining_bytes > 0])

        trace("SCHED bdp peer=%d bdp_bytes=%d rtmin_us=%d depth=%d inflight=%d" % (
            pid, event.bdp_bytes, event.rtmin_us,
            pipeline_depth_target(peer), len(peer.inflight)))

    elif isinstance(event, TimerFired):
        for pid, tcpi in event.peer_tcp_infos.items():
            if pid in state.peers:
                update_peer_tcp_info(state, state.peers[pid], tcpi)

        if event.peer_id is None:
            # Rebalance timer. Skip if no tcp_info has changed since last rebalance.
            state.rebalance_timer_active = False
            if state.tcp_info_generation != state.last_rebalance_generation:
                state.last_rebalance_generation = state.tcp_info_generation
                active = [p for p in state.payloads.values() if p.remaining_bytes > 0]
                actions += rebalance(state, active)
                actions += schedule_payloads(state, active)
        else:
            # Stall-check or recovery timer for a specific peer.
            pid = event.peer_id
            state.active_stall_timers.discard(pid)
            peer = state.peers[pid]

            if isinstance(peer.status, Snubbing):
                if maybe_promote_snubbing(state, pid):
                    actions += schedule_payloads(state,
                        [p for p in state.payloads.values()
                         if p.remaining_bytes > 0 and pid in p.peers_offered])
            else:
                # Stall check: is the next reply (MSG_RESPONSE or
                # MSG_CANCELED_RESPONSE) overdue? Uses peer.inflight,
                # which includes cancelled-but-pending chunks — we
                # expect replies to those too. The deadline was baked
                # in at the chunk's assignment time, reflecting how
                # much pending work was already ahead of it.
                any_overdue = (peer.inflight and
                               event.time >= peer.deadlines[0])
                if any_overdue:
                    head = peer.inflight[0]
                    overdue_ms = (event.time - peer.deadlines[0]) * 1000
                    deadline_budget_ms = (peer.deadlines[0]
                        - head.assignments[pid].when) * 1000 if pid in head.assignments else -1
                    throughput = estimated_throughput(peer)
                    trace("SCHED stall peer=%d overdue_ms=%.1f deadline_budget_ms=%.1f "
                          "chunk_size=%d throughput=%.0f inflight=%d assigned=%d" % (
                        pid, overdue_ms, deadline_budget_ms,
                        head.size, throughput,
                        len(peer.inflight), len(peer.assigned_inflight)))
                    prev_count = peer.status.stall_count if isinstance(peer.status, Probationary) else 0
                    new_count = prev_count + 1
                    was_probing = isinstance(peer.status, Probing)
                    peer.status = Snubbing(stall_count=new_count)
                    if was_probing:
                        # Abort probe without doubling next probe size.
                        actions.append(AbortProbe(peer_id=pid))
                    affected = {}  # payload_hash -> PayloadState
                    for chunk in list(peer.assigned_inflight):
                        affected[chunk.payload.payload_hash] = chunk.payload
                        actions.append(do_cancel(state, pid, chunk))
                    # Assign the freed chunks to other peers.
                    actions += schedule_payloads(state,
                        [p for p in affected.values() if p.remaining_bytes > 0])
                    # Schedule recovery with exponential backoff.
                    delay = round_up_timer(min(SNUBBING_MAX_MS,
                        SNUBBING_BASE_MS * (2 ** (new_count - 1))))
                    state.active_stall_timers.add(pid)
                    actions.append(SetTimer(pid, delay))

    actions += ensure_stall_timers(state)
    actions += ensure_rebalance_timer(state)
    return actions
