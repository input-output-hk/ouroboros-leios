//! Handshake mini-protocol (protocol ID 0).
//!
//! Negotiates the protocol version and parameters between two peers.
//! Runs exactly once at connection startup as a single request/response
//! exchange. Handshake messages must fit in a single MUX segment (they
//! are transmitted before the multiplexer is fully initialized).

pub mod codec;
pub mod n2n;

use std::collections::BTreeMap;
use std::fmt::Debug;
use std::time::Duration;

use crate::mux::{CodecRecv, CodecSend};
use crate::protocols::{Agency, Protocol, ProtocolError, Role, Runner};

/// Handshake protocol ID in the multiplexer.
pub const PROTOCOL_ID: u16 = 0;

/// Max handshake message size per spec (4 × 1440 TCP segments).
pub const SIZE_LIMIT: usize = 5760;

/// Handshake timeout per spec.
pub const TIMEOUT: Duration = Duration::from_secs(10);

// --- State machine ---

/// Handshake protocol states.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum State {
    /// Client proposes versions. Client has agency.
    Propose,
    /// Server confirms or refuses. Server has agency.
    Confirm,
    /// Protocol complete. Nobody has agency.
    Done,
}

/// Handshake protocol messages.
#[derive(Debug, Clone)]
pub enum Message {
    /// Client proposes supported versions (version number → opaque CBOR params).
    ProposeVersions(VersionTable),
    /// Server accepts a version and returns negotiated parameters.
    AcceptVersion(u64, Vec<u8>),
    /// Server refuses all proposed versions.
    Refuse(RefuseReason),
    /// Response to a version query.
    QueryReply(VersionTable),
}

/// A version table maps version numbers to their opaque CBOR-encoded parameters.
/// Keys must be in ascending order (BTreeMap guarantees this).
pub type VersionTable = BTreeMap<u64, Vec<u8>>;

/// Reason for refusing a handshake.
#[derive(Debug, Clone)]
pub enum RefuseReason {
    /// No common version found. Contains the server's supported version numbers.
    VersionMismatch(Vec<u64>),
    /// Server couldn't decode version parameters.
    HandshakeDecodeError(u64, String),
    /// Server policy refused the proposed parameters.
    Refused(u64, String),
}

// --- Protocol trait implementation ---

/// The handshake protocol definition.
pub struct Handshake;

impl Protocol for Handshake {
    type State = State;
    type Message = Message;

    fn initial_state() -> State {
        State::Propose
    }

    fn agency(state: &State) -> Agency {
        match state {
            State::Propose => Agency::Client,
            State::Confirm => Agency::Server,
            State::Done => Agency::Nobody,
        }
    }

    fn transition(state: &State, msg: &Message) -> Result<State, ProtocolError> {
        match (state, msg) {
            (State::Propose, Message::ProposeVersions(_)) => Ok(State::Confirm),
            (State::Confirm, Message::AcceptVersion(_, _)) => Ok(State::Done),
            (State::Confirm, Message::Refuse(_)) => Ok(State::Done),
            (State::Confirm, Message::QueryReply(_)) => Ok(State::Done),
            _ => Err(ProtocolError::InvalidMessage(format!(
                "{msg:?} not valid in state {state:?}"
            ))),
        }
    }

    fn size_limit(_state: &State) -> usize {
        SIZE_LIMIT
    }

    fn timeout(_state: &State) -> Option<Duration> {
        Some(TIMEOUT)
    }
}

// --- Client / Server ---

/// Result of a successful handshake from the client's perspective.
#[derive(Debug, Clone)]
pub enum HandshakeResult {
    /// Server accepted a version.
    Accepted {
        version_number: u64,
        params: Vec<u8>,
    },
    /// Server refused all versions.
    Refused(RefuseReason),
    /// Server replied with its version table (query mode).
    QueryReply(VersionTable),
}

/// Run the handshake as a client: propose versions, receive response.
pub async fn run_client(
    codec_send: CodecSend,
    codec_recv: CodecRecv,
    versions: VersionTable,
) -> Result<HandshakeResult, ProtocolError> {
    let mut runner = Runner::<Handshake>::new(Role::Client, codec_send, codec_recv);

    // Send our version proposal.
    runner.send(&Message::ProposeVersions(versions)).await?;

    // Receive the server's response.
    let response = runner.recv().await?;

    match response {
        Message::AcceptVersion(version_number, params) => Ok(HandshakeResult::Accepted {
            version_number,
            params,
        }),
        Message::Refuse(reason) => Ok(HandshakeResult::Refused(reason)),
        Message::QueryReply(table) => Ok(HandshakeResult::QueryReply(table)),
        other => Err(ProtocolError::InvalidMessage(format!(
            "unexpected response: {other:?}"
        ))),
    }
}

/// Run the handshake as a server: receive proposal, respond.
///
/// The `negotiate` callback receives the client's version table and must
/// return either an acceptance (version number + encoded params) or a
/// refuse reason.
pub async fn run_server<F>(
    codec_send: CodecSend,
    codec_recv: CodecRecv,
    negotiate: F,
) -> Result<(u64, Vec<u8>), ProtocolError>
where
    F: FnOnce(&VersionTable) -> Result<(u64, Vec<u8>), RefuseReason>,
{
    let mut runner = Runner::<Handshake>::new(Role::Server, codec_send, codec_recv);

    // Receive the client's proposal.
    let proposal = runner.recv().await?;

    let client_versions = match &proposal {
        Message::ProposeVersions(versions) => versions,
        other => {
            return Err(ProtocolError::InvalidMessage(format!(
                "expected ProposeVersions, got {other:?}"
            )));
        }
    };

    // Run the negotiation callback.
    match negotiate(client_versions) {
        Ok((version_number, params)) => {
            runner
                .send(&Message::AcceptVersion(version_number, params.clone()))
                .await?;
            Ok((version_number, params))
        }
        Err(reason) => {
            runner.send(&Message::Refuse(reason.clone())).await?;
            Err(ProtocolError::InvalidMessage(format!(
                "negotiation refused: {reason:?}"
            )))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bearer::mem::MemBearer;
    use crate::mux::scheduler::RoundRobin;
    use crate::mux::{Mux, MuxConfig, ProtocolConfig, MODE_INITIATOR, MODE_RESPONDER};

    fn test_config() -> MuxConfig {
        MuxConfig {
            sdu_timeout: std::time::Duration::from_secs(2),
            ..MuxConfig::default()
        }
    }

    fn make_handshake_mux_pair() -> (
        (CodecSend, CodecRecv),
        (CodecSend, CodecRecv),
        crate::mux::RunningMux,
        crate::mux::RunningMux,
    ) {
        let (bearer_a, bearer_b) = MemBearer::pair();

        let proto = ProtocolConfig {
            id: PROTOCOL_ID,
            priority: 0,
            ingress_limit: SIZE_LIMIT,
            egress_queue_size: 4,
        };

        let mut mux_a = Mux::new(test_config(), RoundRobin::default(), MODE_INITIATOR);
        let (send_a, recv_a) = mux_a.register(&proto);
        let running_a = mux_a.run(bearer_a);

        let mut mux_b = Mux::new(test_config(), RoundRobin::default(), MODE_RESPONDER);
        let (send_b, recv_b) = mux_b.register(&proto);
        let running_b = mux_b.run(bearer_b);

        (
            (CodecSend::new(send_a), CodecRecv::new(recv_a)),
            (CodecSend::new(send_b), CodecRecv::new(recv_b)),
            running_a,
            running_b,
        )
    }

    #[tokio::test]
    async fn handshake_client_server_success() {
        let ((cs, cr), (ss, sr), ra, rb) = make_handshake_mux_pair();

        let magic = n2n::MAINNET_MAGIC;

        let client_handle = tokio::spawn(async move {
            let versions = n2n::version_table(&n2n::VersionData {
                network_magic: magic,
                initiator_only_diffusion_mode: false,
                peer_sharing: 0,
                query: false,
            });
            run_client(cs, cr, versions).await
        });

        let server_handle = tokio::spawn(async move {
            run_server(ss, sr, |client_versions| {
                n2n::negotiate(client_versions, magic)
            })
            .await
        });

        let client_result = client_handle.await.unwrap().unwrap();
        let server_result = server_handle.await.unwrap().unwrap();

        // Client should have received acceptance.
        match client_result {
            HandshakeResult::Accepted {
                version_number,
                params,
            } => {
                assert_eq!(version_number, n2n::VERSION_V15);
                let data = n2n::VersionData::decode(&params).unwrap();
                assert_eq!(data.network_magic, magic);
            }
            other => panic!("expected Accepted, got {other:?}"),
        }

        // Server should have returned the negotiated version.
        assert_eq!(server_result.0, n2n::VERSION_V15);

        ra.abort();
        rb.abort();
    }

    #[tokio::test]
    async fn handshake_magic_mismatch() {
        let ((cs, cr), (ss, sr), ra, rb) = make_handshake_mux_pair();

        let client_handle = tokio::spawn(async move {
            let versions = n2n::version_table(&n2n::VersionData {
                network_magic: n2n::MAINNET_MAGIC,
                initiator_only_diffusion_mode: false,
                peer_sharing: 0,
                query: false,
            });
            run_client(cs, cr, versions).await
        });

        let server_handle = tokio::spawn(async move {
            run_server(ss, sr, |client_versions| {
                // Server expects testnet magic — mismatch!
                n2n::negotiate(client_versions, n2n::TESTNET_MAGIC)
            })
            .await
        });

        let client_result = client_handle.await.unwrap().unwrap();

        // Client should have received a refusal.
        match client_result {
            HandshakeResult::Refused(RefuseReason::Refused(version, msg)) => {
                assert_eq!(version, n2n::VERSION_V15);
                assert!(msg.contains("magic mismatch"), "msg: {msg}");
            }
            other => panic!("expected Refused, got {other:?}"),
        }

        // Server should have returned an error.
        assert!(server_handle.await.unwrap().is_err());

        ra.abort();
        rb.abort();
    }
}
