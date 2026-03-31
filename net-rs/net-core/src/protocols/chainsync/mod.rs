//! ChainSync mini-protocol (protocol ID 2).
//!
//! Allows a consumer (client) to follow the chain of a producer (server).
//! The consumer requests headers one at a time and tracks the chain tip.
//! Supports intersection finding for initial sync and fork handling via
//! rollback messages.

pub mod codec;

use std::time::Duration;

use crate::protocols::{Agency, Protocol, ProtocolError, Runner};
use crate::types::{Point, Tip, WrappedHeader};

/// ChainSync protocol ID in the multiplexer.
pub const PROTOCOL_ID: u16 = 2;

/// Ingress buffer limit for ChainSync (per spec).
pub const INGRESS_LIMIT: usize = 462_000;

/// Max message size for all ChainSync states.
pub const SIZE_LIMIT: usize = 65_535;

/// Timeout for StIdle (long — consumer may be downloading a large range).
pub const TIMEOUT_IDLE: Duration = Duration::from_secs(3673);

/// Timeout for StCanAwait (server waits until a new block arrives).
pub const TIMEOUT_CAN_AWAIT: Duration = Duration::from_secs(3673);

/// Timeout for StMustReply (midpoint of spec's 601-911s range).
pub const TIMEOUT_MUST_REPLY: Duration = Duration::from_secs(756);

/// Timeout for StIntersect.
pub const TIMEOUT_INTERSECT: Duration = Duration::from_secs(10);

// --- State machine ---

/// ChainSync protocol states.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum State {
    /// Consumer can request next header or find intersection. Client has agency.
    StIdle,
    /// Producer can reply with data or say "wait". Server has agency.
    StCanAwait,
    /// Producer must reply (no AwaitReply allowed). Server has agency.
    StMustReply,
    /// Producer searches for intersection point. Server has agency.
    StIntersect,
    /// Protocol complete. Nobody has agency.
    StDone,
}

/// ChainSync protocol messages.
#[derive(Debug, Clone)]
pub enum Message {
    /// Consumer requests the next header. [0]
    MsgRequestNext,
    /// Producer says "wait, no new data yet". [1]
    MsgAwaitReply,
    /// Producer sends a new header. [2, header, tip]
    MsgRollForward { header: WrappedHeader, tip: Tip },
    /// Producer says chain rolled back. [3, point, tip]
    MsgRollBackward { point: Point, tip: Tip },
    /// Consumer requests intersection. [4, points]
    MsgFindIntersect { points: Vec<Point> },
    /// Producer found an intersection. [5, point, tip]
    MsgIntersectFound { point: Point, tip: Tip },
    /// Producer found no intersection. [6, tip]
    MsgIntersectNotFound { tip: Tip },
    /// Consumer is done. [7]
    MsgDone,
}

// --- Protocol trait ---

/// The ChainSync protocol definition.
pub struct ChainSync;

impl Protocol for ChainSync {
    type State = State;
    type Message = Message;

    fn initial_state() -> State {
        State::StIdle
    }

    fn agency(state: &State) -> Agency {
        match state {
            State::StIdle => Agency::Client,
            State::StCanAwait => Agency::Server,
            State::StMustReply => Agency::Server,
            State::StIntersect => Agency::Server,
            State::StDone => Agency::Nobody,
        }
    }

    fn transition(state: &State, msg: &Message) -> Result<State, ProtocolError> {
        match (state, msg) {
            (State::StIdle, Message::MsgRequestNext) => Ok(State::StCanAwait),
            (State::StIdle, Message::MsgFindIntersect { .. }) => Ok(State::StIntersect),
            (State::StIdle, Message::MsgDone) => Ok(State::StDone),

            (State::StCanAwait, Message::MsgAwaitReply) => Ok(State::StMustReply),
            (State::StCanAwait, Message::MsgRollForward { .. }) => Ok(State::StIdle),
            (State::StCanAwait, Message::MsgRollBackward { .. }) => Ok(State::StIdle),

            (State::StMustReply, Message::MsgRollForward { .. }) => Ok(State::StIdle),
            (State::StMustReply, Message::MsgRollBackward { .. }) => Ok(State::StIdle),

            (State::StIntersect, Message::MsgIntersectFound { .. }) => Ok(State::StIdle),
            (State::StIntersect, Message::MsgIntersectNotFound { .. }) => Ok(State::StIdle),

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
            State::StIdle => Some(TIMEOUT_IDLE),
            State::StCanAwait => Some(TIMEOUT_CAN_AWAIT),
            State::StMustReply => Some(TIMEOUT_MUST_REPLY),
            State::StIntersect => Some(TIMEOUT_INTERSECT),
            State::StDone => None,
        }
    }
}

// --- Client helpers ---

/// Event returned by `request_next`.
#[derive(Debug, Clone)]
pub enum ChainSyncEvent {
    RollForward { header: WrappedHeader, tip: Tip },
    RollBackward { point: Point, tip: Tip },
}

/// Find an intersection point. Returns `Some((point, tip))` if found, `None` if not.
pub async fn find_intersection(
    runner: &mut Runner<ChainSync>,
    points: Vec<Point>,
) -> Result<Option<(Point, Tip)>, ProtocolError> {
    runner.send(&Message::MsgFindIntersect { points }).await?;
    let msg = runner.recv().await?;
    match msg {
        Message::MsgIntersectFound { point, tip } => Ok(Some((point, tip))),
        Message::MsgIntersectNotFound { .. } => Ok(None),
        other => Err(ProtocolError::InvalidMessage(format!(
            "expected IntersectFound/NotFound, got {other:?}"
        ))),
    }
}

/// Request the next header. Handles MsgAwaitReply transparently by waiting
/// for the subsequent MsgRollForward/MsgRollBackward.
pub async fn request_next(runner: &mut Runner<ChainSync>) -> Result<ChainSyncEvent, ProtocolError> {
    runner.send(&Message::MsgRequestNext).await?;
    let msg = runner.recv().await?;
    match msg {
        Message::MsgRollForward { header, tip } => Ok(ChainSyncEvent::RollForward { header, tip }),
        Message::MsgRollBackward { point, tip } => Ok(ChainSyncEvent::RollBackward { point, tip }),
        Message::MsgAwaitReply => {
            // Now in StMustReply — wait for the actual response.
            let msg = runner.recv().await?;
            match msg {
                Message::MsgRollForward { header, tip } => {
                    Ok(ChainSyncEvent::RollForward { header, tip })
                }
                Message::MsgRollBackward { point, tip } => {
                    Ok(ChainSyncEvent::RollBackward { point, tip })
                }
                other => Err(ProtocolError::InvalidMessage(format!(
                    "expected RollForward/RollBackward after AwaitReply, got {other:?}"
                ))),
            }
        }
        other => Err(ProtocolError::InvalidMessage(format!(
            "expected RollForward/RollBackward/AwaitReply, got {other:?}"
        ))),
    }
}

/// Send MsgDone to terminate the protocol.
pub async fn done(runner: &mut Runner<ChainSync>) -> Result<(), ProtocolError> {
    runner.send(&Message::MsgDone).await
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bearer::mem::MemBearer;
    use crate::mux::scheduler::{RoundRobin, TrafficClass};
    use crate::mux::{
        CodecRecv, CodecSend, Mux, MuxConfig, ProtocolConfig, MODE_INITIATOR, MODE_RESPONDER,
    };
    use crate::protocols::Role;

    #[test]
    fn agency_correct() {
        assert_eq!(ChainSync::agency(&State::StIdle), Agency::Client);
        assert_eq!(ChainSync::agency(&State::StCanAwait), Agency::Server);
        assert_eq!(ChainSync::agency(&State::StMustReply), Agency::Server);
        assert_eq!(ChainSync::agency(&State::StIntersect), Agency::Server);
        assert_eq!(ChainSync::agency(&State::StDone), Agency::Nobody);
    }

    #[test]
    fn valid_transitions() {
        // StIdle transitions
        assert_eq!(
            ChainSync::transition(&State::StIdle, &Message::MsgRequestNext).unwrap(),
            State::StCanAwait
        );
        assert_eq!(
            ChainSync::transition(
                &State::StIdle,
                &Message::MsgFindIntersect { points: vec![] }
            )
            .unwrap(),
            State::StIntersect
        );
        assert_eq!(
            ChainSync::transition(&State::StIdle, &Message::MsgDone).unwrap(),
            State::StDone
        );

        // StCanAwait transitions
        let tip = Tip {
            point: Point::Origin,
            block_no: 0,
        };
        assert_eq!(
            ChainSync::transition(&State::StCanAwait, &Message::MsgAwaitReply).unwrap(),
            State::StMustReply
        );
        assert_eq!(
            ChainSync::transition(
                &State::StCanAwait,
                &Message::MsgRollForward {
                    header: WrappedHeader::opaque(vec![]),
                    tip: tip.clone(),
                }
            )
            .unwrap(),
            State::StIdle
        );
        assert_eq!(
            ChainSync::transition(
                &State::StCanAwait,
                &Message::MsgRollBackward {
                    point: Point::Origin,
                    tip: tip.clone(),
                }
            )
            .unwrap(),
            State::StIdle
        );

        // StMustReply transitions
        assert_eq!(
            ChainSync::transition(
                &State::StMustReply,
                &Message::MsgRollForward {
                    header: WrappedHeader::opaque(vec![]),
                    tip: tip.clone(),
                }
            )
            .unwrap(),
            State::StIdle
        );
        assert_eq!(
            ChainSync::transition(
                &State::StMustReply,
                &Message::MsgRollBackward {
                    point: Point::Origin,
                    tip: tip.clone(),
                }
            )
            .unwrap(),
            State::StIdle
        );

        // StIntersect transitions
        assert_eq!(
            ChainSync::transition(
                &State::StIntersect,
                &Message::MsgIntersectFound {
                    point: Point::Origin,
                    tip: tip.clone(),
                }
            )
            .unwrap(),
            State::StIdle
        );
        assert_eq!(
            ChainSync::transition(&State::StIntersect, &Message::MsgIntersectNotFound { tip })
                .unwrap(),
            State::StIdle
        );
    }

    #[test]
    fn invalid_transitions() {
        assert!(ChainSync::transition(&State::StIdle, &Message::MsgAwaitReply).is_err());
        assert!(ChainSync::transition(&State::StCanAwait, &Message::MsgRequestNext).is_err());
        assert!(ChainSync::transition(&State::StMustReply, &Message::MsgAwaitReply).is_err());
        assert!(ChainSync::transition(&State::StIntersect, &Message::MsgRequestNext).is_err());
    }

    #[test]
    fn size_limits() {
        assert_eq!(ChainSync::size_limit(&State::StIdle), 65_535);
        assert_eq!(ChainSync::size_limit(&State::StCanAwait), 65_535);
        assert_eq!(ChainSync::size_limit(&State::StMustReply), 65_535);
        assert_eq!(ChainSync::size_limit(&State::StIntersect), 65_535);
    }

    #[test]
    fn timeouts() {
        assert_eq!(ChainSync::timeout(&State::StIdle), Some(TIMEOUT_IDLE));
        assert_eq!(
            ChainSync::timeout(&State::StCanAwait),
            Some(TIMEOUT_CAN_AWAIT)
        );
        assert_eq!(
            ChainSync::timeout(&State::StMustReply),
            Some(TIMEOUT_MUST_REPLY)
        );
        assert_eq!(
            ChainSync::timeout(&State::StIntersect),
            Some(TIMEOUT_INTERSECT)
        );
        assert_eq!(ChainSync::timeout(&State::StDone), None);
    }

    fn test_config() -> MuxConfig {
        MuxConfig {
            sdu_timeout: std::time::Duration::from_secs(2),
            ..MuxConfig::default()
        }
    }

    fn make_chainsync_mux_pair() -> (
        (CodecSend, CodecRecv),
        (CodecSend, CodecRecv),
        crate::mux::RunningMux,
        crate::mux::RunningMux,
    ) {
        let (bearer_a, bearer_b) = MemBearer::pair();

        let proto = ProtocolConfig {
            id: PROTOCOL_ID,
            traffic_class: TrafficClass::Priority,
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
    async fn chainsync_intersection_and_roll_forward() {
        let ((cs, cr), (ss, sr), ra, rb) = make_chainsync_mux_pair();

        let tip = Tip {
            point: Point::Specific {
                slot: 100,
                hash: [0x01; 32],
            },
            block_no: 50,
        };
        let header_bytes = vec![0x82, 0x06, 0xd8, 0x18, 0x44, 0xde, 0xad, 0xbe, 0xef];

        let tip_clone = tip.clone();
        let header_clone = header_bytes.clone();

        // Server: respond to intersection, then send one roll-forward, then receive done.
        let server = tokio::spawn(async move {
            let mut runner = Runner::<ChainSync>::new(Role::Server, ss, sr);

            let msg = runner.recv().await.unwrap();
            assert!(matches!(msg, Message::MsgFindIntersect { .. }));

            runner
                .send(&Message::MsgIntersectFound {
                    point: Point::Origin,
                    tip: tip_clone.clone(),
                })
                .await
                .unwrap();

            let msg = runner.recv().await.unwrap();
            assert!(matches!(msg, Message::MsgRequestNext));

            runner
                .send(&Message::MsgRollForward {
                    header: WrappedHeader::opaque(header_clone),
                    tip: tip_clone,
                })
                .await
                .unwrap();

            let msg = runner.recv().await.unwrap();
            assert!(matches!(msg, Message::MsgDone));
        });

        // Client: find intersection, request one header, done.
        let client = tokio::spawn(async move {
            let mut runner = Runner::<ChainSync>::new(Role::Client, cs, cr);

            let result = find_intersection(&mut runner, vec![Point::Origin])
                .await
                .unwrap();
            assert!(result.is_some());
            let (point, _tip) = result.unwrap();
            assert_eq!(point, Point::Origin);

            let event = request_next(&mut runner).await.unwrap();
            match event {
                ChainSyncEvent::RollForward { header, tip: t } => {
                    assert_eq!(header, WrappedHeader::opaque(header_bytes));
                    assert_eq!(t, tip);
                }
                other => panic!("expected RollForward, got {other:?}"),
            }

            done(&mut runner).await.unwrap();
        });

        client.await.unwrap();
        server.await.unwrap();
        ra.abort();
        rb.abort();
    }

    #[tokio::test]
    async fn chainsync_await_reply() {
        let ((cs, cr), (ss, sr), ra, rb) = make_chainsync_mux_pair();

        let tip = Tip {
            point: Point::Origin,
            block_no: 0,
        };
        let tip_clone = tip.clone();

        // Server: send AwaitReply then RollForward.
        let server = tokio::spawn(async move {
            let mut runner = Runner::<ChainSync>::new(Role::Server, ss, sr);

            let msg = runner.recv().await.unwrap();
            assert!(matches!(msg, Message::MsgRequestNext));

            runner.send(&Message::MsgAwaitReply).await.unwrap();
            runner
                .send(&Message::MsgRollForward {
                    header: WrappedHeader::opaque(vec![0x80]),
                    tip: tip_clone,
                })
                .await
                .unwrap();

            let msg = runner.recv().await.unwrap();
            assert!(matches!(msg, Message::MsgDone));
        });

        // Client: request_next should handle AwaitReply transparently.
        let client = tokio::spawn(async move {
            let mut runner = Runner::<ChainSync>::new(Role::Client, cs, cr);

            let event = request_next(&mut runner).await.unwrap();
            assert!(matches!(event, ChainSyncEvent::RollForward { .. }));

            done(&mut runner).await.unwrap();
        });

        client.await.unwrap();
        server.await.unwrap();
        ra.abort();
        rb.abort();
    }
}
