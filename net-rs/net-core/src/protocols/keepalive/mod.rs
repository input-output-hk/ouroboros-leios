//! KeepAlive mini-protocol (protocol ID 8).
//!
//! Periodic ping/pong to measure round-trip time and detect dead connections.
//! The client sends a cookie, the server echoes it back.

pub mod codec;

use std::time::Duration;

use crate::protocols::{Agency, Protocol, ProtocolError, Runner};

/// KeepAlive protocol ID in the multiplexer.
pub const PROTOCOL_ID: u16 = 8;

/// Ingress buffer limit for KeepAlive (per spec).
pub const INGRESS_LIMIT: usize = 1_408;

/// Max message size for all KeepAlive states.
pub const SIZE_LIMIT: usize = 65_535;

/// Timeout for StClient (time to send next keep-alive or done).
pub const TIMEOUT_CLIENT: Duration = Duration::from_secs(97);

/// Timeout for StServer (time to respond with keep-alive response).
pub const TIMEOUT_SERVER: Duration = Duration::from_secs(60);

// --- State machine ---

/// KeepAlive protocol states.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum State {
    /// Client can send a keep-alive request or terminate. Client has agency.
    StClient,
    /// Server must respond with a keep-alive response. Server has agency.
    StServer,
    /// Protocol complete. Nobody has agency.
    StDone,
}

/// KeepAlive protocol messages.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Message {
    /// Client sends a keep-alive with a cookie. [0, cookie]
    MsgKeepAlive { cookie: u16 },
    /// Server echoes the cookie. [1, cookie]
    MsgKeepAliveResponse { cookie: u16 },
    /// Client terminates. [2]
    MsgDone,
}

// --- Protocol trait ---

/// The KeepAlive protocol definition.
pub struct KeepAlive;

impl Protocol for KeepAlive {
    type State = State;
    type Message = Message;

    fn initial_state() -> State {
        State::StClient
    }

    fn agency(state: &State) -> Agency {
        match state {
            State::StClient => Agency::Client,
            State::StServer => Agency::Server,
            State::StDone => Agency::Nobody,
        }
    }

    fn transition(state: &State, msg: &Message) -> Result<State, ProtocolError> {
        match (state, msg) {
            (State::StClient, Message::MsgKeepAlive { .. }) => Ok(State::StServer),
            (State::StClient, Message::MsgDone) => Ok(State::StDone),
            (State::StServer, Message::MsgKeepAliveResponse { .. }) => Ok(State::StClient),
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
            State::StClient => Some(TIMEOUT_CLIENT),
            State::StServer => Some(TIMEOUT_SERVER),
            State::StDone => None,
        }
    }
}

// --- Client helper ---

/// Send a keep-alive ping and wait for the response.
/// Returns the round-trip duration and verifies the cookie matches.
pub async fn keep_alive(
    runner: &mut Runner<KeepAlive>,
    cookie: u16,
) -> Result<Duration, ProtocolError> {
    let start = std::time::Instant::now();
    runner.send(&Message::MsgKeepAlive { cookie }).await?;
    let msg = runner.recv().await?;
    let rtt = start.elapsed();

    match msg {
        Message::MsgKeepAliveResponse {
            cookie: response_cookie,
        } => {
            if response_cookie != cookie {
                return Err(ProtocolError::InvalidMessage(format!(
                    "cookie mismatch: sent {cookie}, got {response_cookie}"
                )));
            }
            Ok(rtt)
        }
        other => Err(ProtocolError::InvalidMessage(format!(
            "expected KeepAliveResponse, got {other:?}"
        ))),
    }
}

/// Send MsgDone to terminate the protocol.
pub async fn done(runner: &mut Runner<KeepAlive>) -> Result<(), ProtocolError> {
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
        assert_eq!(KeepAlive::agency(&State::StClient), Agency::Client);
        assert_eq!(KeepAlive::agency(&State::StServer), Agency::Server);
        assert_eq!(KeepAlive::agency(&State::StDone), Agency::Nobody);
    }

    #[test]
    fn valid_transitions() {
        assert_eq!(
            KeepAlive::transition(&State::StClient, &Message::MsgKeepAlive { cookie: 42 }).unwrap(),
            State::StServer
        );
        assert_eq!(
            KeepAlive::transition(&State::StClient, &Message::MsgDone).unwrap(),
            State::StDone
        );
        assert_eq!(
            KeepAlive::transition(
                &State::StServer,
                &Message::MsgKeepAliveResponse { cookie: 42 }
            )
            .unwrap(),
            State::StClient
        );
    }

    #[test]
    fn invalid_transitions() {
        assert!(KeepAlive::transition(
            &State::StClient,
            &Message::MsgKeepAliveResponse { cookie: 0 }
        )
        .is_err());
        assert!(
            KeepAlive::transition(&State::StServer, &Message::MsgKeepAlive { cookie: 0 }).is_err()
        );
        assert!(KeepAlive::transition(&State::StServer, &Message::MsgDone).is_err());
    }

    #[test]
    fn timeouts() {
        assert_eq!(KeepAlive::timeout(&State::StClient), Some(TIMEOUT_CLIENT));
        assert_eq!(KeepAlive::timeout(&State::StServer), Some(TIMEOUT_SERVER));
        assert_eq!(KeepAlive::timeout(&State::StDone), None);
    }

    fn test_config() -> MuxConfig {
        MuxConfig {
            sdu_timeout: std::time::Duration::from_secs(2),
            ..MuxConfig::default()
        }
    }

    fn make_keepalive_mux_pair() -> (
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
    async fn keepalive_ping_pong() {
        let ((cs, cr), (ss, sr), ra, rb) = make_keepalive_mux_pair();

        let server = tokio::spawn(async move {
            let mut runner = Runner::<KeepAlive>::new(Role::Server, ss, sr);

            for _ in 0..2 {
                let msg = runner.recv().await.unwrap();
                match msg {
                    Message::MsgKeepAlive { cookie } => {
                        runner
                            .send(&Message::MsgKeepAliveResponse { cookie })
                            .await
                            .unwrap();
                    }
                    other => panic!("expected KeepAlive, got {other:?}"),
                }
            }

            let msg = runner.recv().await.unwrap();
            assert!(matches!(msg, Message::MsgDone));
        });

        let client = tokio::spawn(async move {
            let mut runner = Runner::<KeepAlive>::new(Role::Client, cs, cr);

            let rtt1 = keep_alive(&mut runner, 1234).await.unwrap();
            assert!(rtt1.as_millis() < 1000);

            let rtt2 = keep_alive(&mut runner, 5678).await.unwrap();
            assert!(rtt2.as_millis() < 1000);

            done(&mut runner).await.unwrap();
        });

        client.await.unwrap();
        server.await.unwrap();
        ra.abort();
        rb.abort();
    }

    #[tokio::test]
    async fn keepalive_cookie_mismatch() {
        let ((cs, cr), (ss, sr), ra, rb) = make_keepalive_mux_pair();

        let server = tokio::spawn(async move {
            let mut runner = Runner::<KeepAlive>::new(Role::Server, ss, sr);

            let msg = runner.recv().await.unwrap();
            assert!(matches!(msg, Message::MsgKeepAlive { .. }));

            // Respond with wrong cookie intentionally.
            runner
                .send(&Message::MsgKeepAliveResponse { cookie: 9999 })
                .await
                .unwrap();
        });

        let client = tokio::spawn(async move {
            let mut runner = Runner::<KeepAlive>::new(Role::Client, cs, cr);
            let result = keep_alive(&mut runner, 1234).await;
            assert!(result.is_err());
        });

        client.await.unwrap();
        server.await.unwrap();
        ra.abort();
        rb.abort();
    }
}
