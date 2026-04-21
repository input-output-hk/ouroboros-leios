use std::sync::atomic::{AtomicU64, Ordering};

/// Per-shard network statistics, updated by the sequential engine at each
/// slot boundary and read by nodes for memory diagnostics.
#[derive(Debug)]
struct ShardStats {
    connections: AtomicU64,
    active_connections: AtomicU64,
    queued_messages: AtomicU64,
    queued_bytes: AtomicU64,
}

impl ShardStats {
    fn new() -> Self {
        Self {
            connections: AtomicU64::new(0),
            active_connections: AtomicU64::new(0),
            queued_messages: AtomicU64::new(0),
            queued_bytes: AtomicU64::new(0),
        }
    }
}

/// Aggregates network queue statistics across all shards.
#[derive(Debug)]
///
/// Each shard's sequential engine calls `update_shard()` at slot boundaries.
/// Nodes call `totals()` to get the process-wide aggregate for logging.
pub struct NetworkStatsCollector {
    shards: Vec<ShardStats>,
}

impl NetworkStatsCollector {
    pub fn new(shard_count: usize) -> Self {
        Self {
            shards: (0..shard_count).map(|_| ShardStats::new()).collect(),
        }
    }

    /// Called by the sequential engine to update stats for one shard.
    pub fn update_shard(
        &self,
        shard_idx: usize,
        connections: u64,
        active_connections: u64,
        queued_messages: u64,
        queued_bytes: u64,
    ) {
        let s = &self.shards[shard_idx];
        s.connections.store(connections, Ordering::Relaxed);
        s.active_connections.store(active_connections, Ordering::Relaxed);
        s.queued_messages.store(queued_messages, Ordering::Relaxed);
        s.queued_bytes.store(queued_bytes, Ordering::Relaxed);
    }

    /// Returns (connections, active_connections, queued_messages, queued_bytes)
    /// summed across all shards.
    pub fn totals(&self) -> (u64, u64, u64, u64) {
        let mut connections = 0u64;
        let mut active = 0u64;
        let mut msgs = 0u64;
        let mut bytes = 0u64;
        for s in &self.shards {
            connections += s.connections.load(Ordering::Relaxed);
            active += s.active_connections.load(Ordering::Relaxed);
            msgs += s.queued_messages.load(Ordering::Relaxed);
            bytes += s.queued_bytes.load(Ordering::Relaxed);
        }
        (connections, active, msgs, bytes)
    }
}
