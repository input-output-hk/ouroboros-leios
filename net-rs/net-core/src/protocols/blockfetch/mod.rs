//! BlockFetch mini-protocol (protocol ID 3).
//!
//! Allows a client to request ranges of blocks from a server.
//! The server streams blocks one at a time within a batch.

pub mod codec;

use std::time::Duration;

use crate::protocol::{Agency, Protocol, ProtocolError, Runner};
use crate::types::{BlockBody, Point};

/// BlockFetch protocol ID in the multiplexer.
pub const PROTOCOL_ID: u16 = 3;

/// Ingress buffer limit for BlockFetch (per spec).
pub const INGRESS_LIMIT: usize = 230_686_940;

/// Max message size in StIdle and StBusy.
pub const SIZE_LIMIT_SMALL: usize = 65_535;

/// Max message size in StStreaming (blocks are large).
pub const SIZE_LIMIT_STREAMING: usize = 2_500_000;

/// Timeout for StBusy.
pub const TIMEOUT_BUSY: Duration = Duration::from_secs(60);

/// Timeout for StStreaming.
pub const TIMEOUT_STREAMING: Duration = Duration::from_secs(60);

// --- State machine ---

/// BlockFetch protocol states.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum State {
    /// Client can request a range or terminate. Client has agency.
    StIdle,
    /// Server decides if it has the blocks. Server has agency.
    StBusy,
    /// Server streams blocks. Server has agency.
    StStreaming,
    /// Protocol complete. Nobody has agency.
    StDone,
}

/// BlockFetch protocol messages.
#[derive(Debug, Clone)]
pub enum Message {
    /// Client requests a range of blocks. [0, from, to]
    MsgRequestRange { from: Point, to: Point },
    /// Client is done. [1]
    MsgClientDone,
    /// Server starts streaming blocks. [2]
    MsgStartBatch,
    /// Server has no blocks for the requested range. [3]
    MsgNoBlocks,
    /// Server sends one block. [4, block]
    MsgBlock { body: BlockBody },
    /// Server finished streaming the batch. [5]
    MsgBatchDone,
}

// --- Protocol trait ---

/// The BlockFetch protocol definition.
pub struct BlockFetch;

impl Protocol for BlockFetch {
    type State = State;
    type Message = Message;

    fn initial_state() -> State {
        State::StIdle
    }

    fn agency(state: &State) -> Agency {
        match state {
            State::StIdle => Agency::Client,
            State::StBusy => Agency::Server,
            State::StStreaming => Agency::Server,
            State::StDone => Agency::Nobody,
        }
    }

    fn transition(state: &State, msg: &Message) -> Result<State, ProtocolError> {
        match (state, msg) {
            (State::StIdle, Message::MsgRequestRange { .. }) => Ok(State::StBusy),
            (State::StIdle, Message::MsgClientDone) => Ok(State::StDone),

            (State::StBusy, Message::MsgStartBatch) => Ok(State::StStreaming),
            (State::StBusy, Message::MsgNoBlocks) => Ok(State::StIdle),

            (State::StStreaming, Message::MsgBlock { .. }) => Ok(State::StStreaming),
            (State::StStreaming, Message::MsgBatchDone) => Ok(State::StIdle),

            _ => Err(ProtocolError::InvalidMessage(format!(
                "{msg:?} not valid in state {state:?}"
            ))),
        }
    }

    fn size_limit(state: &State) -> usize {
        match state {
            State::StIdle | State::StBusy => SIZE_LIMIT_SMALL,
            State::StStreaming => SIZE_LIMIT_STREAMING,
            State::StDone => 0,
        }
    }

    fn timeout(state: &State) -> Option<Duration> {
        match state {
            State::StIdle => None, // client has agency, no timeout
            State::StBusy => Some(TIMEOUT_BUSY),
            State::StStreaming => Some(TIMEOUT_STREAMING),
            State::StDone => None,
        }
    }
}

// --- Client helpers ---

/// Request a range of blocks. Returns true if the server starts a batch,
/// false if the server has no blocks for the requested range.
pub async fn request_range(
    runner: &mut Runner<BlockFetch>,
    from: Point,
    to: Point,
) -> Result<bool, ProtocolError> {
    runner.send(&Message::MsgRequestRange { from, to }).await?;
    let msg = runner.recv().await?;
    match msg {
        Message::MsgStartBatch => Ok(true),
        Message::MsgNoBlocks => Ok(false),
        other => Err(ProtocolError::InvalidMessage(format!(
            "expected StartBatch/NoBlocks, got {other:?}"
        ))),
    }
}

/// Receive the next block in a batch. Returns `Some(body)` for each block,
/// or `None` when the batch is complete.
pub async fn recv_block(
    runner: &mut Runner<BlockFetch>,
) -> Result<Option<BlockBody>, ProtocolError> {
    let msg = runner.recv().await?;
    match msg {
        Message::MsgBlock { body } => Ok(Some(body)),
        Message::MsgBatchDone => Ok(None),
        other => Err(ProtocolError::InvalidMessage(format!(
            "expected Block/BatchDone, got {other:?}"
        ))),
    }
}

/// Send MsgClientDone to terminate the protocol.
pub async fn done(runner: &mut Runner<BlockFetch>) -> Result<(), ProtocolError> {
    runner.send(&Message::MsgClientDone).await
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bearer::mem::MemBearer;
    use crate::codec::{CodecRecv, CodecSend};
    use crate::mux::scheduler::RoundRobin;
    use crate::mux::{Mux, MuxConfig, ProtocolConfig, MODE_INITIATOR, MODE_RESPONDER};
    use crate::protocol::Role;

    #[test]
    fn agency_correct() {
        assert_eq!(BlockFetch::agency(&State::StIdle), Agency::Client);
        assert_eq!(BlockFetch::agency(&State::StBusy), Agency::Server);
        assert_eq!(BlockFetch::agency(&State::StStreaming), Agency::Server);
        assert_eq!(BlockFetch::agency(&State::StDone), Agency::Nobody);
    }

    #[test]
    fn valid_transitions() {
        // StIdle
        assert_eq!(
            BlockFetch::transition(
                &State::StIdle,
                &Message::MsgRequestRange {
                    from: Point::Origin,
                    to: Point::Origin,
                }
            )
            .unwrap(),
            State::StBusy
        );
        assert_eq!(
            BlockFetch::transition(&State::StIdle, &Message::MsgClientDone).unwrap(),
            State::StDone
        );

        // StBusy
        assert_eq!(
            BlockFetch::transition(&State::StBusy, &Message::MsgStartBatch).unwrap(),
            State::StStreaming
        );
        assert_eq!(
            BlockFetch::transition(&State::StBusy, &Message::MsgNoBlocks).unwrap(),
            State::StIdle
        );

        // StStreaming
        assert_eq!(
            BlockFetch::transition(
                &State::StStreaming,
                &Message::MsgBlock {
                    body: BlockBody(vec![]),
                }
            )
            .unwrap(),
            State::StStreaming
        );
        assert_eq!(
            BlockFetch::transition(&State::StStreaming, &Message::MsgBatchDone).unwrap(),
            State::StIdle
        );
    }

    #[test]
    fn invalid_transitions() {
        assert!(BlockFetch::transition(&State::StIdle, &Message::MsgStartBatch).is_err());
        assert!(BlockFetch::transition(&State::StBusy, &Message::MsgClientDone).is_err());
        assert!(BlockFetch::transition(
            &State::StStreaming,
            &Message::MsgRequestRange {
                from: Point::Origin,
                to: Point::Origin,
            }
        )
        .is_err());
    }

    #[test]
    fn size_limits() {
        assert_eq!(BlockFetch::size_limit(&State::StIdle), 65_535);
        assert_eq!(BlockFetch::size_limit(&State::StBusy), 65_535);
        assert_eq!(BlockFetch::size_limit(&State::StStreaming), 2_500_000);
    }

    #[test]
    fn timeouts() {
        assert_eq!(BlockFetch::timeout(&State::StIdle), None);
        assert_eq!(BlockFetch::timeout(&State::StBusy), Some(TIMEOUT_BUSY));
        assert_eq!(
            BlockFetch::timeout(&State::StStreaming),
            Some(TIMEOUT_STREAMING)
        );
        assert_eq!(BlockFetch::timeout(&State::StDone), None);
    }

    fn test_config() -> MuxConfig {
        MuxConfig {
            sdu_timeout: std::time::Duration::from_secs(2),
            ..MuxConfig::default()
        }
    }

    fn make_blockfetch_mux_pair() -> (
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
    async fn blockfetch_request_and_stream() {
        let ((cs, cr), (ss, sr), ra, rb) = make_blockfetch_mux_pair();

        let block1 = BlockBody(vec![0xd8, 0x18, 0x43, 0x01, 0x02, 0x03]);
        let block2 = BlockBody(vec![0xd8, 0x18, 0x43, 0x04, 0x05, 0x06]);
        let block1c = block1.clone();
        let block2c = block2.clone();

        // Server: receive request, stream two blocks.
        let server = tokio::spawn(async move {
            let mut runner = Runner::<BlockFetch>::new(Role::Server, ss, sr);

            let msg = runner.recv().await.unwrap();
            assert!(matches!(msg, Message::MsgRequestRange { .. }));

            runner.send(&Message::MsgStartBatch).await.unwrap();
            runner
                .send(&Message::MsgBlock { body: block1c })
                .await
                .unwrap();
            runner
                .send(&Message::MsgBlock { body: block2c })
                .await
                .unwrap();
            runner.send(&Message::MsgBatchDone).await.unwrap();

            let msg = runner.recv().await.unwrap();
            assert!(matches!(msg, Message::MsgClientDone));
        });

        // Client: request range, receive blocks.
        let client = tokio::spawn(async move {
            let mut runner = Runner::<BlockFetch>::new(Role::Client, cs, cr);

            let has_blocks = request_range(
                &mut runner,
                Point::Specific {
                    slot: 1,
                    hash: [0x01; 32],
                },
                Point::Specific {
                    slot: 2,
                    hash: [0x02; 32],
                },
            )
            .await
            .unwrap();
            assert!(has_blocks);

            let b1 = recv_block(&mut runner).await.unwrap();
            assert_eq!(b1, Some(block1));

            let b2 = recv_block(&mut runner).await.unwrap();
            assert_eq!(b2, Some(block2));

            let b3 = recv_block(&mut runner).await.unwrap();
            assert_eq!(b3, None); // BatchDone

            done(&mut runner).await.unwrap();
        });

        client.await.unwrap();
        server.await.unwrap();
        ra.abort();
        rb.abort();
    }

    #[tokio::test]
    async fn blockfetch_no_blocks() {
        let ((cs, cr), (ss, sr), ra, rb) = make_blockfetch_mux_pair();

        let server = tokio::spawn(async move {
            let mut runner = Runner::<BlockFetch>::new(Role::Server, ss, sr);
            let _ = runner.recv().await.unwrap();
            runner.send(&Message::MsgNoBlocks).await.unwrap();
            let _ = runner.recv().await.unwrap();
        });

        let client = tokio::spawn(async move {
            let mut runner = Runner::<BlockFetch>::new(Role::Client, cs, cr);

            let has_blocks = request_range(&mut runner, Point::Origin, Point::Origin)
                .await
                .unwrap();
            assert!(!has_blocks);

            done(&mut runner).await.unwrap();
        });

        client.await.unwrap();
        server.await.unwrap();
        ra.abort();
        rb.abort();
    }
}
