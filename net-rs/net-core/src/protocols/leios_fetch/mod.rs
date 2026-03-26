//! LeiosFetch mini-protocol (protocol ID 19).
//!
//! Request-response protocol for fetching Leios data. Client-driven and
//! pipelineable. Supports fetching individual EBs, selective transactions
//! via bitmap addressing, votes, and certified EB ranges.

pub mod codec;

use std::collections::BTreeMap;
use std::time::Duration;

use crate::protocols::{Agency, Protocol, ProtocolError, Runner};
use crate::types::Point;

/// LeiosFetch protocol ID in the multiplexer.
pub const PROTOCOL_ID: u16 = 19;

/// Ingress buffer limit for LeiosFetch (16 MB — carries full EBs and tx lists).
pub const INGRESS_LIMIT: usize = 16_777_216;

/// Max message size for request messages (StIdle).
pub const SIZE_LIMIT_SMALL: usize = 65_535;

/// Max message size for delivery messages (StBlock, StBlockTxs, StVotes, StBlockRange).
pub const SIZE_LIMIT_LARGE: usize = 16_777_216;

/// Maximum entries in a bitmap TX request.
pub const MAX_BITMAP_ENTRIES: usize = 1024;

/// Maximum number of transactions in a delivery.
pub const MAX_TRANSACTIONS: usize = 65_536;

/// Maximum size of a single opaque transaction blob.
pub const MAX_TRANSACTION_SIZE: usize = 65_536;

/// Maximum size of an opaque EB block blob.
pub const MAX_BLOCK_SIZE: usize = 16_777_216;

/// Maximum number of vote IDs in a request or votes in a delivery.
pub const MAX_VOTES: usize = 1024;

/// Maximum size of an opaque voter ID.
pub const MAX_VOTER_ID_SIZE: usize = 256;

/// Maximum size of an opaque vote blob.
pub const MAX_VOTE_SIZE: usize = 1024;

/// Timeout for server states (120s — block range may involve large transfers).
pub const TIMEOUT_SERVER: Duration = Duration::from_secs(120);

// --- State machine ---

/// LeiosFetch protocol states.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum State {
    /// Client can request any Leios data or terminate. Client has agency.
    StIdle,
    /// Server must deliver an EB. Server has agency.
    StBlock,
    /// Server must deliver transactions. Server has agency.
    StBlockTxs,
    /// Server must deliver votes. Server has agency.
    StVotes,
    /// Server must deliver next or last block+txs in range. Server has agency.
    StBlockRange,
    /// Protocol complete. Nobody has agency.
    StDone,
}

/// LeiosFetch protocol messages.
#[derive(Debug, Clone)]
pub enum Message {
    /// Client requests an EB. [0, point]
    MsgLeiosBlockRequest { point: Point },
    /// Server delivers an EB. [1, block]
    MsgLeiosBlock { block: Vec<u8> },
    /// Client requests selective transactions via bitmap. [2, point, bitmap]
    MsgLeiosBlockTxsRequest {
        point: Point,
        bitmap: BTreeMap<u16, u64>,
    },
    /// Server delivers transactions. [3, [tx, ...]]
    MsgLeiosBlockTxs { transactions: Vec<Vec<u8>> },
    /// Client requests votes. [4, [(slot, voter_id), ...]]
    MsgLeiosVotesRequest { votes: Vec<(u64, Vec<u8>)> },
    /// Server delivers votes. [5, [vote, ...]]
    MsgLeiosVoteDelivery { votes: Vec<Vec<u8>> },
    /// Client requests a certified EB range. [6, start_slot, end_slot, start_hash, end_hash]
    MsgLeiosBlockRangeRequest {
        start_slot: u64,
        end_slot: u64,
        start_hash: [u8; 32],
        end_hash: [u8; 32],
    },
    /// Server delivers next block+txs in range (more to follow). [7, block, [tx, ...]]
    MsgLeiosNextBlockAndTxsInRange {
        block: Vec<u8>,
        transactions: Vec<Vec<u8>>,
    },
    /// Server delivers last block+txs in range (end of sequence). [8, block, [tx, ...]]
    MsgLeiosLastBlockAndTxsInRange {
        block: Vec<u8>,
        transactions: Vec<Vec<u8>>,
    },
    /// Client terminates. [9]
    MsgDone,
}

// --- Protocol trait ---

/// The LeiosFetch protocol definition.
pub struct LeiosFetch;

impl Protocol for LeiosFetch {
    type State = State;
    type Message = Message;

    fn initial_state() -> State {
        State::StIdle
    }

    fn agency(state: &State) -> Agency {
        match state {
            State::StIdle => Agency::Client,
            State::StBlock => Agency::Server,
            State::StBlockTxs => Agency::Server,
            State::StVotes => Agency::Server,
            State::StBlockRange => Agency::Server,
            State::StDone => Agency::Nobody,
        }
    }

    fn transition(state: &State, msg: &Message) -> Result<State, ProtocolError> {
        match (state, msg) {
            (State::StIdle, Message::MsgLeiosBlockRequest { .. }) => Ok(State::StBlock),
            (State::StBlock, Message::MsgLeiosBlock { .. }) => Ok(State::StIdle),
            (State::StIdle, Message::MsgLeiosBlockTxsRequest { .. }) => Ok(State::StBlockTxs),
            (State::StBlockTxs, Message::MsgLeiosBlockTxs { .. }) => Ok(State::StIdle),
            (State::StIdle, Message::MsgLeiosVotesRequest { .. }) => Ok(State::StVotes),
            (State::StVotes, Message::MsgLeiosVoteDelivery { .. }) => Ok(State::StIdle),
            (State::StIdle, Message::MsgLeiosBlockRangeRequest { .. }) => Ok(State::StBlockRange),
            (State::StBlockRange, Message::MsgLeiosNextBlockAndTxsInRange { .. }) => {
                Ok(State::StBlockRange)
            }
            (State::StBlockRange, Message::MsgLeiosLastBlockAndTxsInRange { .. }) => {
                Ok(State::StIdle)
            }
            (State::StIdle, Message::MsgDone) => Ok(State::StDone),
            _ => Err(ProtocolError::InvalidMessage(format!(
                "{msg:?} not valid in state {state:?}"
            ))),
        }
    }

    fn size_limit(state: &State) -> usize {
        match state {
            State::StIdle => SIZE_LIMIT_SMALL,
            State::StBlock | State::StBlockTxs | State::StVotes | State::StBlockRange => {
                SIZE_LIMIT_LARGE
            }
            State::StDone => 0,
        }
    }

    fn timeout(state: &State) -> Option<Duration> {
        match state {
            State::StIdle => None,
            State::StBlock | State::StBlockTxs | State::StVotes | State::StBlockRange => {
                Some(TIMEOUT_SERVER)
            }
            State::StDone => None,
        }
    }
}

// --- Client helpers ---

/// Fetch a single EB from the server.
pub async fn fetch_block(
    runner: &mut Runner<LeiosFetch>,
    point: Point,
) -> Result<Vec<u8>, ProtocolError> {
    runner
        .send(&Message::MsgLeiosBlockRequest { point })
        .await?;
    let msg = runner.recv().await?;
    match msg {
        Message::MsgLeiosBlock { block } => Ok(block),
        other => Err(ProtocolError::InvalidMessage(format!(
            "expected MsgLeiosBlock, got {other:?}"
        ))),
    }
}

/// Fetch selective transactions from an EB using bitmap addressing.
pub async fn fetch_block_txs(
    runner: &mut Runner<LeiosFetch>,
    point: Point,
    bitmap: BTreeMap<u16, u64>,
) -> Result<Vec<Vec<u8>>, ProtocolError> {
    runner
        .send(&Message::MsgLeiosBlockTxsRequest { point, bitmap })
        .await?;
    let msg = runner.recv().await?;
    match msg {
        Message::MsgLeiosBlockTxs { transactions } => Ok(transactions),
        other => Err(ProtocolError::InvalidMessage(format!(
            "expected MsgLeiosBlockTxs, got {other:?}"
        ))),
    }
}

/// Fetch votes from the server.
pub async fn fetch_votes(
    runner: &mut Runner<LeiosFetch>,
    votes: Vec<(u64, Vec<u8>)>,
) -> Result<Vec<Vec<u8>>, ProtocolError> {
    runner
        .send(&Message::MsgLeiosVotesRequest { votes })
        .await?;
    let msg = runner.recv().await?;
    match msg {
        Message::MsgLeiosVoteDelivery { votes } => Ok(votes),
        other => Err(ProtocolError::InvalidMessage(format!(
            "expected MsgLeiosVoteDelivery, got {other:?}"
        ))),
    }
}

/// Fetch a certified EB range. Collects all blocks+txs until the last one.
pub async fn fetch_block_range(
    runner: &mut Runner<LeiosFetch>,
    start_slot: u64,
    end_slot: u64,
    start_hash: [u8; 32],
    end_hash: [u8; 32],
) -> Result<Vec<(Vec<u8>, Vec<Vec<u8>>)>, ProtocolError> {
    runner
        .send(&Message::MsgLeiosBlockRangeRequest {
            start_slot,
            end_slot,
            start_hash,
            end_hash,
        })
        .await?;

    let mut results = Vec::new();
    loop {
        let msg = runner.recv().await?;
        match msg {
            Message::MsgLeiosNextBlockAndTxsInRange {
                block,
                transactions,
            } => {
                results.push((block, transactions));
            }
            Message::MsgLeiosLastBlockAndTxsInRange {
                block,
                transactions,
            } => {
                results.push((block, transactions));
                return Ok(results);
            }
            other => {
                return Err(ProtocolError::InvalidMessage(format!(
                    "expected MsgLeiosNextBlockAndTxsInRange or MsgLeiosLastBlockAndTxsInRange, got {other:?}"
                )));
            }
        }
    }
}

/// Send MsgDone to terminate the protocol.
pub async fn done(runner: &mut Runner<LeiosFetch>) -> Result<(), ProtocolError> {
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
    use crate::types::Point;

    fn test_hash() -> [u8; 32] {
        let mut h = [0u8; 32];
        h[0] = 0xAB;
        h[31] = 0xCD;
        h
    }

    fn test_hash2() -> [u8; 32] {
        let mut h = [0u8; 32];
        h[0] = 0xDE;
        h[31] = 0xEF;
        h
    }

    #[test]
    fn agency_correct() {
        assert_eq!(LeiosFetch::agency(&State::StIdle), Agency::Client);
        assert_eq!(LeiosFetch::agency(&State::StBlock), Agency::Server);
        assert_eq!(LeiosFetch::agency(&State::StBlockTxs), Agency::Server);
        assert_eq!(LeiosFetch::agency(&State::StVotes), Agency::Server);
        assert_eq!(LeiosFetch::agency(&State::StBlockRange), Agency::Server);
        assert_eq!(LeiosFetch::agency(&State::StDone), Agency::Nobody);
    }

    #[test]
    fn valid_transitions() {
        // Block request/response
        assert_eq!(
            LeiosFetch::transition(
                &State::StIdle,
                &Message::MsgLeiosBlockRequest {
                    point: Point::Specific {
                        slot: 1,
                        hash: [0; 32],
                    },
                }
            )
            .unwrap(),
            State::StBlock
        );
        assert_eq!(
            LeiosFetch::transition(
                &State::StBlock,
                &Message::MsgLeiosBlock { block: vec![0x80] }
            )
            .unwrap(),
            State::StIdle
        );
        // BlockTxs request/response
        assert_eq!(
            LeiosFetch::transition(
                &State::StIdle,
                &Message::MsgLeiosBlockTxsRequest {
                    point: Point::Specific {
                        slot: 1,
                        hash: [0; 32],
                    },
                    bitmap: BTreeMap::new(),
                }
            )
            .unwrap(),
            State::StBlockTxs
        );
        assert_eq!(
            LeiosFetch::transition(
                &State::StBlockTxs,
                &Message::MsgLeiosBlockTxs {
                    transactions: vec![],
                }
            )
            .unwrap(),
            State::StIdle
        );
        // Votes request/response
        assert_eq!(
            LeiosFetch::transition(
                &State::StIdle,
                &Message::MsgLeiosVotesRequest { votes: vec![] }
            )
            .unwrap(),
            State::StVotes
        );
        assert_eq!(
            LeiosFetch::transition(
                &State::StVotes,
                &Message::MsgLeiosVoteDelivery { votes: vec![] }
            )
            .unwrap(),
            State::StIdle
        );
        // Block range: request → next → next → last
        assert_eq!(
            LeiosFetch::transition(
                &State::StIdle,
                &Message::MsgLeiosBlockRangeRequest {
                    start_slot: 1,
                    end_slot: 10,
                    start_hash: [0; 32],
                    end_hash: [0; 32],
                }
            )
            .unwrap(),
            State::StBlockRange
        );
        assert_eq!(
            LeiosFetch::transition(
                &State::StBlockRange,
                &Message::MsgLeiosNextBlockAndTxsInRange {
                    block: vec![],
                    transactions: vec![],
                }
            )
            .unwrap(),
            State::StBlockRange
        );
        assert_eq!(
            LeiosFetch::transition(
                &State::StBlockRange,
                &Message::MsgLeiosLastBlockAndTxsInRange {
                    block: vec![],
                    transactions: vec![],
                }
            )
            .unwrap(),
            State::StIdle
        );
        // Done
        assert_eq!(
            LeiosFetch::transition(&State::StIdle, &Message::MsgDone).unwrap(),
            State::StDone
        );
    }

    #[test]
    fn invalid_transitions() {
        // Server message in client state
        assert!(LeiosFetch::transition(
            &State::StIdle,
            &Message::MsgLeiosBlock { block: vec![0x80] }
        )
        .is_err());
        // Client message in server state
        assert!(LeiosFetch::transition(
            &State::StBlock,
            &Message::MsgLeiosBlockRequest {
                point: Point::Specific {
                    slot: 1,
                    hash: [0; 32]
                },
            }
        )
        .is_err());
        // Wrong server state
        assert!(LeiosFetch::transition(
            &State::StBlock,
            &Message::MsgLeiosBlockTxs {
                transactions: vec![],
            }
        )
        .is_err());
        // Done in server state
        assert!(LeiosFetch::transition(&State::StBlock, &Message::MsgDone).is_err());
        // Next in wrong state
        assert!(LeiosFetch::transition(
            &State::StVotes,
            &Message::MsgLeiosNextBlockAndTxsInRange {
                block: vec![],
                transactions: vec![],
            }
        )
        .is_err());
    }

    #[test]
    fn size_limits() {
        assert_eq!(LeiosFetch::size_limit(&State::StIdle), SIZE_LIMIT_SMALL);
        assert_eq!(LeiosFetch::size_limit(&State::StBlock), SIZE_LIMIT_LARGE);
        assert_eq!(LeiosFetch::size_limit(&State::StBlockTxs), SIZE_LIMIT_LARGE);
        assert_eq!(LeiosFetch::size_limit(&State::StVotes), SIZE_LIMIT_LARGE);
        assert_eq!(
            LeiosFetch::size_limit(&State::StBlockRange),
            SIZE_LIMIT_LARGE
        );
    }

    #[test]
    fn timeouts() {
        assert_eq!(LeiosFetch::timeout(&State::StIdle), None);
        assert_eq!(LeiosFetch::timeout(&State::StBlock), Some(TIMEOUT_SERVER));
        assert_eq!(
            LeiosFetch::timeout(&State::StBlockTxs),
            Some(TIMEOUT_SERVER)
        );
        assert_eq!(LeiosFetch::timeout(&State::StVotes), Some(TIMEOUT_SERVER));
        assert_eq!(
            LeiosFetch::timeout(&State::StBlockRange),
            Some(TIMEOUT_SERVER)
        );
        assert_eq!(LeiosFetch::timeout(&State::StDone), None);
    }

    fn test_config() -> MuxConfig {
        MuxConfig {
            sdu_timeout: std::time::Duration::from_secs(2),
            ..MuxConfig::default()
        }
    }

    fn make_leios_fetch_mux_pair() -> (
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
    async fn leios_fetch_block() {
        let ((cs, cr), (ss, sr), ra, rb) = make_leios_fetch_mux_pair();
        let hash = test_hash();

        let server = tokio::spawn(async move {
            let mut runner = Runner::<LeiosFetch>::new(Role::Server, ss, sr);

            let msg = runner.recv().await.unwrap();
            match msg {
                Message::MsgLeiosBlockRequest { point } => {
                    assert_eq!(point, Point::Specific { slot: 42, hash });
                }
                other => panic!("expected MsgLeiosBlockRequest, got {other:?}"),
            }

            runner
                .send(&Message::MsgLeiosBlock {
                    block: vec![0xEB, 0x01, 0x02],
                })
                .await
                .unwrap();

            let msg = runner.recv().await.unwrap();
            assert!(matches!(msg, Message::MsgDone));
        });

        let client = tokio::spawn(async move {
            let mut runner = Runner::<LeiosFetch>::new(Role::Client, cs, cr);

            let block = fetch_block(&mut runner, Point::Specific { slot: 42, hash })
                .await
                .unwrap();
            assert_eq!(block, vec![0xEB, 0x01, 0x02]);

            done(&mut runner).await.unwrap();
        });

        client.await.unwrap();
        server.await.unwrap();
        ra.abort();
        rb.abort();
    }

    #[tokio::test]
    async fn leios_fetch_block_txs_with_bitmap() {
        let ((cs, cr), (ss, sr), ra, rb) = make_leios_fetch_mux_pair();
        let hash = test_hash();

        let server = tokio::spawn(async move {
            let mut runner = Runner::<LeiosFetch>::new(Role::Server, ss, sr);

            let msg = runner.recv().await.unwrap();
            match msg {
                Message::MsgLeiosBlockTxsRequest { point, bitmap } => {
                    assert_eq!(point, Point::Specific { slot: 100, hash });
                    assert_eq!(bitmap.len(), 2);
                    assert_eq!(bitmap[&0], 0xFF); // first 8 txs
                    assert_eq!(bitmap[&1], 0x01); // tx 64
                }
                other => panic!("expected MsgLeiosBlockTxsRequest, got {other:?}"),
            }

            runner
                .send(&Message::MsgLeiosBlockTxs {
                    transactions: vec![vec![0x01], vec![0x02], vec![0x03]],
                })
                .await
                .unwrap();

            let msg = runner.recv().await.unwrap();
            assert!(matches!(msg, Message::MsgDone));
        });

        let client = tokio::spawn(async move {
            let mut runner = Runner::<LeiosFetch>::new(Role::Client, cs, cr);

            let mut bitmap = BTreeMap::new();
            bitmap.insert(0u16, 0xFFu64);
            bitmap.insert(1u16, 0x01u64);

            let txs = fetch_block_txs(&mut runner, Point::Specific { slot: 100, hash }, bitmap)
                .await
                .unwrap();
            assert_eq!(txs.len(), 3);

            done(&mut runner).await.unwrap();
        });

        client.await.unwrap();
        server.await.unwrap();
        ra.abort();
        rb.abort();
    }

    #[tokio::test]
    async fn leios_fetch_votes() {
        let ((cs, cr), (ss, sr), ra, rb) = make_leios_fetch_mux_pair();

        let server = tokio::spawn(async move {
            let mut runner = Runner::<LeiosFetch>::new(Role::Server, ss, sr);

            let msg = runner.recv().await.unwrap();
            match msg {
                Message::MsgLeiosVotesRequest { votes } => {
                    assert_eq!(votes.len(), 2);
                    assert_eq!(votes[0], (10, vec![0xAA]));
                    assert_eq!(votes[1], (20, vec![0xBB]));
                }
                other => panic!("expected MsgLeiosVotesRequest, got {other:?}"),
            }

            runner
                .send(&Message::MsgLeiosVoteDelivery {
                    votes: vec![vec![0x01, 0x02], vec![0x03, 0x04]],
                })
                .await
                .unwrap();

            let msg = runner.recv().await.unwrap();
            assert!(matches!(msg, Message::MsgDone));
        });

        let client = tokio::spawn(async move {
            let mut runner = Runner::<LeiosFetch>::new(Role::Client, cs, cr);

            let vote_ids = vec![(10, vec![0xAA]), (20, vec![0xBB])];
            let votes = fetch_votes(&mut runner, vote_ids).await.unwrap();
            assert_eq!(votes.len(), 2);
            assert_eq!(votes[0], vec![0x01, 0x02]);
            assert_eq!(votes[1], vec![0x03, 0x04]);

            done(&mut runner).await.unwrap();
        });

        client.await.unwrap();
        server.await.unwrap();
        ra.abort();
        rb.abort();
    }

    #[tokio::test]
    async fn leios_fetch_block_range() {
        let ((cs, cr), (ss, sr), ra, rb) = make_leios_fetch_mux_pair();

        let server = tokio::spawn(async move {
            let mut runner = Runner::<LeiosFetch>::new(Role::Server, ss, sr);

            let msg = runner.recv().await.unwrap();
            match msg {
                Message::MsgLeiosBlockRangeRequest {
                    start_slot,
                    end_slot,
                    ..
                } => {
                    assert_eq!(start_slot, 10);
                    assert_eq!(end_slot, 12);
                }
                other => panic!("expected MsgLeiosBlockRangeRequest, got {other:?}"),
            }

            // Send 2 blocks: next, then last
            runner
                .send(&Message::MsgLeiosNextBlockAndTxsInRange {
                    block: vec![0xE1],
                    transactions: vec![vec![0x01]],
                })
                .await
                .unwrap();

            runner
                .send(&Message::MsgLeiosLastBlockAndTxsInRange {
                    block: vec![0xE2],
                    transactions: vec![vec![0x02], vec![0x03]],
                })
                .await
                .unwrap();

            let msg = runner.recv().await.unwrap();
            assert!(matches!(msg, Message::MsgDone));
        });

        let client = tokio::spawn(async move {
            let mut runner = Runner::<LeiosFetch>::new(Role::Client, cs, cr);

            let results = fetch_block_range(&mut runner, 10, 12, test_hash(), test_hash2())
                .await
                .unwrap();

            assert_eq!(results.len(), 2);
            assert_eq!(results[0].0, vec![0xE1]);
            assert_eq!(results[0].1, vec![vec![0x01]]);
            assert_eq!(results[1].0, vec![0xE2]);
            assert_eq!(results[1].1, vec![vec![0x02], vec![0x03]]);

            done(&mut runner).await.unwrap();
        });

        client.await.unwrap();
        server.await.unwrap();
        ra.abort();
        rb.abort();
    }

    #[tokio::test]
    async fn leios_fetch_immediate_done() {
        let ((cs, cr), (ss, sr), ra, rb) = make_leios_fetch_mux_pair();

        let server = tokio::spawn(async move {
            let mut runner = Runner::<LeiosFetch>::new(Role::Server, ss, sr);
            let msg = runner.recv().await.unwrap();
            assert!(matches!(msg, Message::MsgDone));
        });

        let client = tokio::spawn(async move {
            let mut runner = Runner::<LeiosFetch>::new(Role::Client, cs, cr);
            done(&mut runner).await.unwrap();
        });

        client.await.unwrap();
        server.await.unwrap();
        ra.abort();
        rb.abort();
    }
}
