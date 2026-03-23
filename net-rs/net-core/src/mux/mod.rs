pub mod wire;
pub mod channel;
pub mod scheduler;
pub mod egress;
pub mod ingress;

use std::collections::HashMap;
use std::time::{Duration, Instant};

use thiserror::Error;
use tokio::task::JoinHandle;

use crate::bearer::Bearer;
use channel::{ChannelRecv, ChannelSend};
use egress::ProtocolEgress;
use ingress::ProtocolIngress;

/// Mini-protocol identifier (15-bit, 0..32767).
pub type ProtocolId = u16;

/// Priority level for mux scheduling.
pub type Priority = u8;

/// Direction bit for the wire protocol. The high bit of the protocol field
/// distinguishes initiator (0) from responder (0x8000).
pub const MODE_INITIATOR: u16 = 0x0000;
pub const MODE_RESPONDER: u16 = 0x8000;

/// Default SDU (segment) payload size, matching Cardano node's 12KB choice.
pub const DEFAULT_SDU_SIZE: usize = 12_288;

/// Configuration for a single protocol channel within the mux.
#[derive(Debug, Clone)]
pub struct ProtocolConfig {
    pub id: ProtocolId,
    pub priority: Priority,
    /// Maximum bytes that can accumulate in the ingress buffer before the
    /// connection is torn down (protocol violation per spec).
    pub ingress_limit: usize,
    /// Capacity of the egress channel (number of messages that can be queued).
    pub egress_queue_size: usize,
}

/// Top-level mux configuration.
#[derive(Debug, Clone)]
pub struct MuxConfig {
    /// Maximum payload bytes per SDU segment.
    pub sdu_size: usize,
    /// Protocol channels to register.
    pub protocols: Vec<ProtocolConfig>,
    /// Bearer-level timeout for receiving a complete SDU. During handshake
    /// this is 10s; after handshake it becomes 30s.
    pub sdu_timeout: Duration,
}

impl Default for MuxConfig {
    fn default() -> Self {
        Self {
            sdu_size: DEFAULT_SDU_SIZE,
            protocols: Vec::new(),
            sdu_timeout: Duration::from_secs(30),
        }
    }
}

#[derive(Debug, Error)]
pub enum MuxError {
    #[error("I/O error: {0}")]
    Io(#[from] std::io::Error),

    #[error("ingress buffer overflow for protocol {protocol}: {size} bytes exceeds limit {limit}")]
    IngressOverflow {
        protocol: ProtocolId,
        size: usize,
        limit: usize,
    },

    #[error("unknown protocol {0}")]
    UnknownProtocol(ProtocolId),

    #[error("mux shut down")]
    Shutdown,

    #[error("SDU timeout after {0:?}")]
    SduTimeout(Duration),
}

/// A configured but not yet running multiplexer. Call `channel()` to register
/// protocols, then `run()` to start the muxer/demuxer tasks.
pub struct Mux<S: scheduler::Scheduler> {
    config: MuxConfig,
    scheduler: S,
    mode: u16,
    /// Egress state: protocol → (receiver, mode, pending buffer).
    egress_protocols: HashMap<ProtocolId, ProtocolEgress>,
    /// Ingress state: protocol → (sender, byte count, limit).
    ingress_protocols: HashMap<ProtocolId, ProtocolIngress>,
}

impl<S: scheduler::Scheduler> Mux<S> {
    /// Create a new mux with the given config, scheduler, and mode
    /// (MODE_INITIATOR or MODE_RESPONDER).
    pub fn new(config: MuxConfig, scheduler: S, mode: u16) -> Self {
        Self {
            config,
            scheduler,
            mode,
            egress_protocols: HashMap::new(),
            ingress_protocols: HashMap::new(),
        }
    }

    /// Register a protocol and return its channel halves. The protocol will
    /// participate in multiplexing once `run()` is called.
    pub fn register(&mut self, proto_config: &ProtocolConfig) -> (ChannelSend, ChannelRecv) {
        let id = proto_config.id;

        // Egress: protocol writes → mux reads and sends to bearer.
        let (egress_send, egress_recv) =
            tokio::sync::mpsc::channel(proto_config.egress_queue_size);
        self.egress_protocols.insert(
            id,
            ProtocolEgress {
                rx: egress_recv,
                mode: self.mode,
                pending: None,
            },
        );

        // Ingress: mux reads from bearer → protocol reads.
        let (ingress_send, ingress_recv) =
            tokio::sync::mpsc::channel(proto_config.egress_queue_size);
        self.ingress_protocols.insert(
            id,
            ProtocolIngress {
                tx: ingress_send,
                buffered_bytes: 0,
                limit: proto_config.ingress_limit,
            },
        );

        self.scheduler.register(id, proto_config.priority);

        let send = ChannelSend::new(egress_send);
        let recv = ChannelRecv::new(ingress_recv);
        (send, recv)
    }

    /// Start the muxer and demuxer tasks over the given bearer. Returns a
    /// `RunningMux` with handles to the background tasks.
    pub fn run<B: Bearer>(self, bearer: B) -> RunningMux {
        let (reader, writer) = bearer.split();
        let clock = Instant::now();

        let muxer_handle = tokio::spawn(egress::run_muxer(
            writer,
            self.egress_protocols,
            self.scheduler,
            self.config.sdu_size,
            clock,
        ));

        let demuxer_handle = tokio::spawn(ingress::run_demuxer(
            reader,
            self.ingress_protocols,
            self.config.sdu_timeout,
            self.config.sdu_size,
            self.mode,
        ));

        RunningMux {
            muxer: muxer_handle,
            demuxer: demuxer_handle,
        }
    }
}

/// Handle to a running multiplexer. Dropping this will not cancel the tasks;
/// call `shutdown()` explicitly or abort the handles.
pub struct RunningMux {
    muxer: JoinHandle<Result<(), MuxError>>,
    demuxer: JoinHandle<Result<(), MuxError>>,
}

impl RunningMux {
    /// Wait for both tasks to complete. Returns the first error encountered.
    pub async fn join(self) -> Result<(), MuxError> {
        tokio::select! {
            result = self.muxer => {
                result.map_err(|_| MuxError::Shutdown)?
            }
            result = self.demuxer => {
                result.map_err(|_| MuxError::Shutdown)?
            }
        }
    }

    /// Abort both muxer and demuxer tasks.
    pub fn abort(&self) {
        self.muxer.abort();
        self.demuxer.abort();
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bearer::mem::MemBearer;
    use scheduler::RoundRobin;

    #[tokio::test]
    async fn mux_round_trip_single_protocol() {
        let (bearer_a, bearer_b) = MemBearer::pair();

        // Set up mux A (initiator) with one protocol.
        let proto = ProtocolConfig {
            id: 0,
            priority: 0,
            ingress_limit: 65535,
            egress_queue_size: 10,
        };

        let mut mux_a = Mux::new(MuxConfig::default(), RoundRobin::default(), MODE_INITIATOR);
        let (send_a, _recv_a) = mux_a.register(&proto);
        let running_a = mux_a.run(bearer_a);

        // Set up mux B (responder) with the same protocol.
        let mut mux_b = Mux::new(MuxConfig::default(), RoundRobin::default(), MODE_RESPONDER);
        let (_send_b, mut recv_b) = mux_b.register(&proto);
        let running_b = mux_b.run(bearer_b);

        // Send a message from A to B.
        let payload = bytes::Bytes::from_static(b"hello from A");
        send_a.send(payload.clone()).await.unwrap();

        // Receive on B.
        let received = recv_b.recv().await.unwrap();
        assert_eq!(received, payload);

        // Clean up.
        running_a.abort();
        running_b.abort();
    }

    #[tokio::test]
    async fn mux_bidirectional() {
        let (bearer_a, bearer_b) = MemBearer::pair();

        let proto = ProtocolConfig {
            id: 2,
            priority: 0,
            ingress_limit: 65535,
            egress_queue_size: 10,
        };

        let mut mux_a = Mux::new(MuxConfig::default(), RoundRobin::default(), MODE_INITIATOR);
        let (send_a, mut recv_a) = mux_a.register(&proto);
        let running_a = mux_a.run(bearer_a);

        let mut mux_b = Mux::new(MuxConfig::default(), RoundRobin::default(), MODE_RESPONDER);
        let (send_b, mut recv_b) = mux_b.register(&proto);
        let running_b = mux_b.run(bearer_b);

        // A → B
        send_a
            .send(bytes::Bytes::from_static(b"A to B"))
            .await
            .unwrap();
        let msg = recv_b.recv().await.unwrap();
        assert_eq!(msg, &b"A to B"[..]);

        // B → A
        send_b
            .send(bytes::Bytes::from_static(b"B to A"))
            .await
            .unwrap();
        let msg = recv_a.recv().await.unwrap();
        assert_eq!(msg, &b"B to A"[..]);

        running_a.abort();
        running_b.abort();
    }

    #[tokio::test]
    async fn mux_multiple_protocols() {
        let (bearer_a, bearer_b) = MemBearer::pair();

        let proto_cs = ProtocolConfig {
            id: 2,
            priority: 0,
            ingress_limit: 65535,
            egress_queue_size: 10,
        };
        let proto_bf = ProtocolConfig {
            id: 3,
            priority: 0,
            ingress_limit: 65535,
            egress_queue_size: 10,
        };

        let mut mux_a = Mux::new(MuxConfig::default(), RoundRobin::default(), MODE_INITIATOR);
        let (send_a_cs, _) = mux_a.register(&proto_cs);
        let (send_a_bf, _) = mux_a.register(&proto_bf);
        let running_a = mux_a.run(bearer_a);

        let mut mux_b = Mux::new(MuxConfig::default(), RoundRobin::default(), MODE_RESPONDER);
        let (_, mut recv_b_cs) = mux_b.register(&proto_cs);
        let (_, mut recv_b_bf) = mux_b.register(&proto_bf);
        let running_b = mux_b.run(bearer_b);

        // Send on different protocols.
        send_a_cs
            .send(bytes::Bytes::from_static(b"chainsync"))
            .await
            .unwrap();
        send_a_bf
            .send(bytes::Bytes::from_static(b"blockfetch"))
            .await
            .unwrap();

        // Each protocol receives its own data.
        let cs_msg = recv_b_cs.recv().await.unwrap();
        let bf_msg = recv_b_bf.recv().await.unwrap();
        assert_eq!(cs_msg, &b"chainsync"[..]);
        assert_eq!(bf_msg, &b"blockfetch"[..]);

        running_a.abort();
        running_b.abort();
    }
}

