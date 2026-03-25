pub mod channel;
pub mod codec;
pub mod egress;
pub mod ingress;
pub mod scheduler;
pub mod wire;

pub use codec::{CodecRecv, CodecSend};

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

/// Key for routing mux channels: (protocol_id, mode_bit).
/// In unidirectional mode, each protocol ID has one entry.
/// In duplex mode, a protocol ID may have two entries (one per direction).
pub type ChannelKey = (ProtocolId, u16);

/// A configured but not yet running multiplexer. Call `register()` to register
/// protocols, then `run()` to start the muxer/demuxer tasks.
pub struct Mux<S: scheduler::Scheduler> {
    config: MuxConfig,
    scheduler: S,
    mode: u16,
    /// Egress state: (protocol, mode) → (receiver, mode, pending buffer).
    egress_protocols: HashMap<ChannelKey, ProtocolEgress>,
    /// Ingress state: (protocol, mode) → (sender, byte count, limit).
    /// For ingress, the mode in the key is the *remote* mode (what we expect
    /// to see on incoming segments for this channel).
    ingress_protocols: HashMap<ChannelKey, ProtocolIngress>,
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

    /// Register a protocol using the mux's default mode and return its channel
    /// halves. This is the standard method for unidirectional connections.
    pub fn register(&mut self, proto_config: &ProtocolConfig) -> (ChannelSend, ChannelRecv) {
        self.register_with_mode(proto_config, self.mode)
    }

    /// Register a protocol with an explicit mode (direction) and return its
    /// channel halves. Use this for duplex connections where the same protocol
    /// ID needs channels in both directions.
    pub fn register_with_mode(
        &mut self,
        proto_config: &ProtocolConfig,
        mode: u16,
    ) -> (ChannelSend, ChannelRecv) {
        let id = proto_config.id;

        // Egress: protocol writes → mux reads and sends to bearer.
        // The egress key uses *our* mode (what we stamp on outgoing segments).
        let (egress_send, egress_recv) = tokio::sync::mpsc::channel(proto_config.egress_queue_size);
        self.egress_protocols.insert(
            (id, mode),
            ProtocolEgress {
                rx: egress_recv,
                mode,
                pending: None,
            },
        );

        // Ingress: mux reads from bearer → protocol reads.
        // The ingress key uses the *remote* mode (what we expect on incoming segments).
        let remote_mode = if mode == MODE_INITIATOR {
            MODE_RESPONDER
        } else {
            MODE_INITIATOR
        };
        let ingress_counter = channel::IngressCounter::new();
        let (ingress_send, ingress_recv) =
            tokio::sync::mpsc::channel(proto_config.egress_queue_size);
        self.ingress_protocols.insert(
            (id, remote_mode),
            ProtocolIngress {
                tx: ingress_send,
                counter: ingress_counter.clone(),
                limit: proto_config.ingress_limit,
            },
        );

        self.scheduler.register(id, proto_config.priority);

        let send = ChannelSend::new(egress_send);
        let recv = ChannelRecv::new(ingress_recv, ingress_counter);
        (send, recv)
    }

    /// Start the muxer and demuxer tasks over the given bearer. Returns a
    /// `RunningMux` with handles to the background tasks.
    ///
    /// If either the muxer or demuxer task fails, the other is automatically
    /// aborted and the error is propagated via the `RunningMux`.
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
        ));

        // Spawn a supervisor that aborts the surviving task when one fails.
        let muxer_abort = muxer_handle.abort_handle();
        let demuxer_abort = demuxer_handle.abort_handle();

        let (error_tx, error_rx) = tokio::sync::watch::channel(None);

        let supervisor = tokio::spawn(async move {
            let error = tokio::select! {
                result = muxer_handle => {
                    demuxer_abort.abort();
                    match result {
                        Ok(Ok(())) => None,
                        Ok(Err(e)) => Some(format!("muxer error: {e}")),
                        Err(e) if e.is_cancelled() => None,
                        Err(e) => Some(format!("muxer panic: {e}")),
                    }
                }
                result = demuxer_handle => {
                    muxer_abort.abort();
                    match result {
                        Ok(Ok(())) => None,
                        Ok(Err(e)) => Some(format!("demuxer error: {e}")),
                        Err(e) if e.is_cancelled() => None,
                        Err(e) => Some(format!("demuxer panic: {e}")),
                    }
                }
            };

            if let Some(err) = &error {
                tracing::error!("mux shutdown: {err}");
            }

            let _ = error_tx.send(error);
        });

        RunningMux {
            supervisor,
            error_rx,
        }
    }
}

/// Handle to a running multiplexer. When either the muxer or demuxer task
/// fails, the other is automatically aborted and the error is available
/// via `wait()` or `error()`.
pub struct RunningMux {
    supervisor: JoinHandle<()>,
    error_rx: tokio::sync::watch::Receiver<Option<String>>,
}

impl RunningMux {
    /// Wait for the mux to shut down. Returns the error if one occurred.
    pub async fn wait(&mut self) -> Result<(), MuxError> {
        // Wait for the error channel to be updated.
        let _ = self.error_rx.changed().await;
        match self.error_rx.borrow().as_ref() {
            Some(err) => Err(MuxError::Io(std::io::Error::other(err.clone()))),
            None => Ok(()),
        }
    }

    /// Check if the mux has encountered an error (non-blocking).
    pub fn error(&self) -> Option<String> {
        self.error_rx.borrow().clone()
    }

    /// Abort the mux (both tasks).
    pub fn abort(&self) {
        self.supervisor.abort();
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bearer::mem::MemBearer;
    use scheduler::RoundRobin;

    fn test_config() -> MuxConfig {
        MuxConfig {
            sdu_timeout: Duration::from_secs(2),
            ..MuxConfig::default()
        }
    }

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

        let mut mux_a = Mux::new(test_config(), RoundRobin::default(), MODE_INITIATOR);
        let (send_a, _recv_a) = mux_a.register(&proto);
        let running_a = mux_a.run(bearer_a);

        // Set up mux B (responder) with the same protocol.
        let mut mux_b = Mux::new(test_config(), RoundRobin::default(), MODE_RESPONDER);
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

        let mut mux_a = Mux::new(test_config(), RoundRobin::default(), MODE_INITIATOR);
        let (send_a, mut recv_a) = mux_a.register(&proto);
        let running_a = mux_a.run(bearer_a);

        let mut mux_b = Mux::new(test_config(), RoundRobin::default(), MODE_RESPONDER);
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

        let mut mux_a = Mux::new(test_config(), RoundRobin::default(), MODE_INITIATOR);
        let (send_a_cs, _) = mux_a.register(&proto_cs);
        let (send_a_bf, _) = mux_a.register(&proto_bf);
        let running_a = mux_a.run(bearer_a);

        let mut mux_b = Mux::new(test_config(), RoundRobin::default(), MODE_RESPONDER);
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

    /// Duplex test: register the same protocol in both directions on one
    /// connection. Both sides run protocol 2 as both initiator and responder.
    ///
    /// Wire semantics: register_with_mode(MODE_INITIATOR) creates a channel
    /// that *sends* with mode=0 and *receives* from mode=0x8000 (the remote's
    /// responder). So A's initiator send is received by B's responder recv,
    /// and B's responder send is received by A's initiator recv.
    #[tokio::test]
    async fn mux_duplex_same_protocol_both_directions() {
        let (bearer_a, bearer_b) = MemBearer::pair();

        let proto = ProtocolConfig {
            id: 2,
            priority: 0,
            ingress_limit: 65535,
            egress_queue_size: 10,
        };

        // Side A: register protocol 2 in both directions.
        // init channel: sends mode=0, receives mode=0x8000
        // resp channel: sends mode=0x8000, receives mode=0
        let mut mux_a = Mux::new(test_config(), RoundRobin::default(), MODE_INITIATOR);
        let (send_a_init, mut recv_a_init) = mux_a.register_with_mode(&proto, MODE_INITIATOR);
        let (send_a_resp, mut recv_a_resp) = mux_a.register_with_mode(&proto, MODE_RESPONDER);
        let running_a = mux_a.run(bearer_a);

        // Side B: register protocol 2 in both directions.
        let mut mux_b = Mux::new(test_config(), RoundRobin::default(), MODE_RESPONDER);
        let (send_b_init, mut recv_b_init) = mux_b.register_with_mode(&proto, MODE_INITIATOR);
        let (send_b_resp, mut recv_b_resp) = mux_b.register_with_mode(&proto, MODE_RESPONDER);
        let running_b = mux_b.run(bearer_b);

        // A sends as initiator (mode=0) → B receives on resp channel (ingress key (2, 0)).
        send_a_init
            .send(bytes::Bytes::from_static(b"A init"))
            .await
            .unwrap();
        let msg = recv_b_resp.recv().await.unwrap();
        assert_eq!(msg, &b"A init"[..]);

        // B sends as responder (mode=0x8000) → A receives on init channel (ingress key (2, 0x8000)).
        send_b_resp
            .send(bytes::Bytes::from_static(b"B resp"))
            .await
            .unwrap();
        let msg = recv_a_init.recv().await.unwrap();
        assert_eq!(msg, &b"B resp"[..]);

        // B sends as initiator (mode=0) → A receives on resp channel (ingress key (2, 0)).
        send_b_init
            .send(bytes::Bytes::from_static(b"B init"))
            .await
            .unwrap();
        let msg = recv_a_resp.recv().await.unwrap();
        assert_eq!(msg, &b"B init"[..]);

        // A sends as responder (mode=0x8000) → B receives on init channel (ingress key (2, 0x8000)).
        send_a_resp
            .send(bytes::Bytes::from_static(b"A resp"))
            .await
            .unwrap();
        let msg = recv_b_init.recv().await.unwrap();
        assert_eq!(msg, &b"A resp"[..]);

        running_a.abort();
        running_b.abort();
    }
}
