//! PeerSharing mini-protocol (protocol ID 10).
//!
//! Simple request/reply protocol for peer discovery. The client requests
//! a number of peers, and the server replies with a list of peer addresses.

pub mod codec;

use std::fmt;
use std::net::{Ipv4Addr, Ipv6Addr};
use std::time::Duration;

use crate::protocols::{Agency, Protocol, ProtocolError, Runner};

/// PeerSharing protocol ID in the multiplexer.
pub const PROTOCOL_ID: u16 = 10;

/// Ingress buffer limit for PeerSharing (per spec).
pub const INGRESS_LIMIT: usize = 5_760;

/// Max message size (same for all states).
pub const SIZE_LIMIT: usize = 5_760;

/// Timeout for StBusy (server must reply within 60s).
pub const TIMEOUT_BUSY: Duration = Duration::from_secs(60);

/// Maximum number of peers in a single response (amount is u8).
pub const MAX_PEERS: usize = 255;

// --- Types ---

/// A peer network address (IPv4 or IPv6 with port).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PeerAddress {
    IPv4 { addr: Ipv4Addr, port: u16 },
    IPv6 { addr: Ipv6Addr, port: u16 },
}

impl fmt::Display for PeerAddress {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            PeerAddress::IPv4 { addr, port } => write!(f, "{addr}:{port}"),
            PeerAddress::IPv6 { addr, port } => write!(f, "[{addr}]:{port}"),
        }
    }
}

// --- State machine ---

/// PeerSharing protocol states.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum State {
    /// Client can request peers or terminate.
    StIdle,
    /// Server must reply with peers.
    StBusy,
    /// Protocol complete.
    StDone,
}

/// PeerSharing protocol messages.
#[derive(Debug, Clone)]
pub enum Message {
    /// Client requests peers. [0, amount]
    MsgShareRequest { amount: u8 },
    /// Server replies with peers. [1, [peer, ...]]
    MsgSharePeers { peers: Vec<PeerAddress> },
    /// Client terminates. [2]
    MsgDone,
}

// --- Protocol trait ---

/// The PeerSharing protocol definition.
pub struct PeerSharing;

impl Protocol for PeerSharing {
    type State = State;
    type Message = Message;

    fn initial_state() -> State {
        State::StIdle
    }

    fn agency(state: &State) -> Agency {
        match state {
            State::StIdle => Agency::Client,
            State::StBusy => Agency::Server,
            State::StDone => Agency::Nobody,
        }
    }

    fn transition(state: &State, msg: &Message) -> Result<State, ProtocolError> {
        match (state, msg) {
            (State::StIdle, Message::MsgShareRequest { .. }) => Ok(State::StBusy),
            (State::StIdle, Message::MsgDone) => Ok(State::StDone),
            (State::StBusy, Message::MsgSharePeers { .. }) => Ok(State::StIdle),
            _ => Err(ProtocolError::InvalidMessage(format!(
                "{msg:?} not valid in state {state:?}"
            ))),
        }
    }

    fn size_limit(_state: &State) -> usize {
        SIZE_LIMIT
    }

    fn timeout(state: &State) -> Option<Duration> {
        match state {
            State::StIdle => None,
            State::StBusy => Some(TIMEOUT_BUSY),
            State::StDone => None,
        }
    }
}

// --- Client helpers ---

/// Request peers from the server. Returns the list of peer addresses.
pub async fn share_request(
    runner: &mut Runner<PeerSharing>,
    amount: u8,
) -> Result<Vec<PeerAddress>, ProtocolError> {
    runner.send(&Message::MsgShareRequest { amount }).await?;
    let msg = runner.recv().await?;
    match msg {
        Message::MsgSharePeers { peers } => Ok(peers),
        other => Err(ProtocolError::InvalidMessage(format!(
            "expected MsgSharePeers, got {other:?}"
        ))),
    }
}

/// Send MsgDone to terminate the protocol.
pub async fn done(runner: &mut Runner<PeerSharing>) -> Result<(), ProtocolError> {
    runner.send(&Message::MsgDone).await
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bearer::mem::MemBearer;
    use crate::mux::scheduler::RoundRobin;
    use crate::mux::{
        CodecRecv, CodecSend, Mux, MuxConfig, ProtocolConfig, MODE_INITIATOR, MODE_RESPONDER,
    };
    use crate::protocols::Role;

    #[test]
    fn agency_correct() {
        assert_eq!(PeerSharing::agency(&State::StIdle), Agency::Client);
        assert_eq!(PeerSharing::agency(&State::StBusy), Agency::Server);
        assert_eq!(PeerSharing::agency(&State::StDone), Agency::Nobody);
    }

    #[test]
    fn valid_transitions() {
        assert_eq!(
            PeerSharing::transition(&State::StIdle, &Message::MsgShareRequest { amount: 5 })
                .unwrap(),
            State::StBusy
        );
        assert_eq!(
            PeerSharing::transition(&State::StIdle, &Message::MsgDone).unwrap(),
            State::StDone
        );
        assert_eq!(
            PeerSharing::transition(&State::StBusy, &Message::MsgSharePeers { peers: vec![] })
                .unwrap(),
            State::StIdle
        );
    }

    #[test]
    fn invalid_transitions() {
        assert!(PeerSharing::transition(&State::StBusy, &Message::MsgDone).is_err());
        assert!(
            PeerSharing::transition(&State::StBusy, &Message::MsgShareRequest { amount: 1 })
                .is_err()
        );
        assert!(
            PeerSharing::transition(&State::StIdle, &Message::MsgSharePeers { peers: vec![] })
                .is_err()
        );
    }

    #[test]
    fn size_limits() {
        assert_eq!(PeerSharing::size_limit(&State::StIdle), SIZE_LIMIT);
        assert_eq!(PeerSharing::size_limit(&State::StBusy), SIZE_LIMIT);
    }

    #[test]
    fn timeouts() {
        assert_eq!(PeerSharing::timeout(&State::StIdle), None);
        assert_eq!(PeerSharing::timeout(&State::StBusy), Some(TIMEOUT_BUSY));
        assert_eq!(PeerSharing::timeout(&State::StDone), None);
    }

    fn test_config() -> MuxConfig {
        MuxConfig {
            sdu_timeout: std::time::Duration::from_secs(2),
            ..MuxConfig::default()
        }
    }

    fn make_peersharing_mux_pair() -> (
        (CodecSend, CodecRecv),
        (CodecSend, CodecRecv),
        crate::mux::RunningMux,
        crate::mux::RunningMux,
    ) {
        let (bearer_a, bearer_b) = MemBearer::pair();

        let proto = ProtocolConfig {
            id: PROTOCOL_ID,
            priority: 0,
            ingress_limit: INGRESS_LIMIT,
            egress_queue_size: 16,
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
    async fn peersharing_request_and_reply() {
        let ((cs, cr), (ss, sr), ra, rb) = make_peersharing_mux_pair();

        let server = tokio::spawn(async move {
            let mut runner = Runner::<PeerSharing>::new(Role::Server, ss, sr);

            let msg = runner.recv().await.unwrap();
            match msg {
                Message::MsgShareRequest { amount } => assert_eq!(amount, 5),
                other => panic!("expected MsgShareRequest, got {other:?}"),
            }

            runner
                .send(&Message::MsgSharePeers {
                    peers: vec![
                        PeerAddress::IPv4 {
                            addr: Ipv4Addr::new(10, 0, 0, 1),
                            port: 3001,
                        },
                        PeerAddress::IPv6 {
                            addr: Ipv6Addr::LOCALHOST,
                            port: 3002,
                        },
                    ],
                })
                .await
                .unwrap();

            let msg = runner.recv().await.unwrap();
            assert!(matches!(msg, Message::MsgDone));
        });

        let client = tokio::spawn(async move {
            let mut runner = Runner::<PeerSharing>::new(Role::Client, cs, cr);

            let peers = share_request(&mut runner, 5).await.unwrap();
            assert_eq!(peers.len(), 2);
            assert!(matches!(peers[0], PeerAddress::IPv4 { .. }));
            assert!(matches!(peers[1], PeerAddress::IPv6 { .. }));

            done(&mut runner).await.unwrap();
        });

        client.await.unwrap();
        server.await.unwrap();
        ra.abort();
        rb.abort();
    }

    #[tokio::test]
    async fn peersharing_empty_reply() {
        let ((cs, cr), (ss, sr), ra, rb) = make_peersharing_mux_pair();

        let server = tokio::spawn(async move {
            let mut runner = Runner::<PeerSharing>::new(Role::Server, ss, sr);
            let msg = runner.recv().await.unwrap();
            assert!(matches!(msg, Message::MsgShareRequest { .. }));
            runner
                .send(&Message::MsgSharePeers { peers: vec![] })
                .await
                .unwrap();
            let msg = runner.recv().await.unwrap();
            assert!(matches!(msg, Message::MsgDone));
        });

        let client = tokio::spawn(async move {
            let mut runner = Runner::<PeerSharing>::new(Role::Client, cs, cr);
            let peers = share_request(&mut runner, 3).await.unwrap();
            assert!(peers.is_empty());
            done(&mut runner).await.unwrap();
        });

        client.await.unwrap();
        server.await.unwrap();
        ra.abort();
        rb.abort();
    }
}
