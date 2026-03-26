//! TxSubmission mini-protocol (protocol ID 4, version 2).
//!
//! Pull-based transaction dissemination between full nodes. The server
//! (transaction consumer) requests transaction IDs from the client
//! (transaction provider), then selectively requests full transactions.

pub mod codec;

use std::collections::VecDeque;
use std::time::Duration;

use crate::protocols::{Agency, Protocol, ProtocolError, Runner};

/// TxSubmission protocol ID in the multiplexer.
pub const PROTOCOL_ID: u16 = 4;

/// Ingress buffer limit for TxSubmission (per spec).
pub const INGRESS_LIMIT: usize = 721_424;

/// Max message size in StInit and StIdle.
pub const SIZE_LIMIT_SMALL: usize = 5_760;

/// Max message size in StTxIdsBlocking, StTxIdsNonBlocking, StTxs.
pub const SIZE_LIMIT_LARGE: usize = 2_500_000;

/// Timeout for StTxIdsNonBlocking (client must reply promptly).
pub const TIMEOUT_NON_BLOCKING: Duration = Duration::from_secs(10);

/// Timeout for StTxs (client must reply promptly).
pub const TIMEOUT_TXS: Duration = Duration::from_secs(10);

/// Maximum number of unacknowledged tx ids (flow control window).
pub const MAX_UNACKED: usize = 10;

/// Maximum size of a single encoded tx id.
pub const MAX_TX_ID_SIZE: usize = 128;

/// Maximum size of a single encoded tx body.
pub const MAX_TX_SIZE: usize = 2_500_000;

// --- Types ---

/// Opaque transaction ID stored as raw CBOR bytes.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TxId(pub Vec<u8>);

/// Opaque transaction body stored as raw CBOR bytes.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TxBody(pub Vec<u8>);

/// A transaction ID paired with its serialized size (for flow control).
#[derive(Debug, Clone)]
pub struct TxIdAndSize {
    pub tx_id: TxId,
    pub size: u32,
}

/// A pending transaction waiting to be announced and sent.
#[derive(Debug, Clone)]
pub struct PendingTx {
    pub tx_id: TxId,
    pub body: TxBody,
    pub size: u32,
}

// --- State machine ---

/// TxSubmission protocol states.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum State {
    /// Client sends MsgInit to start the protocol.
    StInit,
    /// Server requests tx ids or full transactions.
    StIdle,
    /// Client provides tx ids (blocking — must have at least one).
    StTxIdsBlocking,
    /// Client provides tx ids (non-blocking — may be empty).
    StTxIdsNonBlocking,
    /// Client provides full transactions.
    StTxs,
    /// Protocol complete.
    StDone,
}

/// TxSubmission protocol messages.
#[derive(Debug, Clone)]
pub enum Message {
    /// Client initiates the protocol. [6]
    MsgInit,
    /// Server requests tx ids (blocking). [0, true, ack, req]
    MsgRequestTxIdsBlocking { ack: u16, req: u16 },
    /// Server requests tx ids (non-blocking). [0, false, ack, req]
    MsgRequestTxIdsNonBlocking { ack: u16, req: u16 },
    /// Client replies with tx ids and their sizes. [1, [...]]
    MsgReplyTxIds { tx_ids: Vec<TxIdAndSize> },
    /// Server requests full transactions by id. [2, [...]]
    MsgRequestTxs { tx_ids: Vec<TxId> },
    /// Client replies with full transactions. [3, [...]]
    MsgReplyTxs { txs: Vec<TxBody> },
    /// Client terminates (only valid in StTxIdsBlocking). [4]
    MsgDone,
}

// --- Protocol trait ---

/// The TxSubmission protocol definition.
pub struct TxSubmission;

impl Protocol for TxSubmission {
    type State = State;
    type Message = Message;

    fn initial_state() -> State {
        State::StInit
    }

    fn agency(state: &State) -> Agency {
        match state {
            State::StInit => Agency::Client,
            State::StIdle => Agency::Server,
            State::StTxIdsBlocking => Agency::Client,
            State::StTxIdsNonBlocking => Agency::Client,
            State::StTxs => Agency::Client,
            State::StDone => Agency::Nobody,
        }
    }

    fn transition(state: &State, msg: &Message) -> Result<State, ProtocolError> {
        match (state, msg) {
            (State::StInit, Message::MsgInit) => Ok(State::StIdle),

            (State::StIdle, Message::MsgRequestTxIdsBlocking { .. }) => Ok(State::StTxIdsBlocking),
            (State::StIdle, Message::MsgRequestTxIdsNonBlocking { .. }) => {
                Ok(State::StTxIdsNonBlocking)
            }
            (State::StIdle, Message::MsgRequestTxs { .. }) => Ok(State::StTxs),

            (State::StTxIdsBlocking, Message::MsgReplyTxIds { .. }) => Ok(State::StIdle),
            (State::StTxIdsBlocking, Message::MsgDone) => Ok(State::StDone),

            (State::StTxIdsNonBlocking, Message::MsgReplyTxIds { .. }) => Ok(State::StIdle),

            (State::StTxs, Message::MsgReplyTxs { .. }) => Ok(State::StIdle),

            _ => Err(ProtocolError::InvalidMessage(format!(
                "{msg:?} not valid in state {state:?}"
            ))),
        }
    }

    fn size_limit(state: &State) -> usize {
        match state {
            State::StInit | State::StIdle => SIZE_LIMIT_SMALL,
            State::StTxIdsBlocking | State::StTxIdsNonBlocking | State::StTxs => SIZE_LIMIT_LARGE,
            State::StDone => 0,
        }
    }

    fn timeout(state: &State) -> Option<Duration> {
        match state {
            State::StInit => None,
            State::StIdle => None,
            State::StTxIdsBlocking => None, // client may block waiting for txs
            State::StTxIdsNonBlocking => Some(TIMEOUT_NON_BLOCKING),
            State::StTxs => Some(TIMEOUT_TXS),
            State::StDone => None,
        }
    }
}

// --- Client helpers ---

/// Run the client (tx provider) side of the TxSubmission protocol.
///
/// Sends MsgInit, then responds to server requests by pulling transactions
/// from `tx_receiver`. When the channel closes and all pending txs have been
/// sent and acknowledged, sends MsgDone and returns.
pub async fn run_client(
    runner: &mut Runner<TxSubmission>,
    tx_receiver: &mut tokio::sync::mpsc::Receiver<PendingTx>,
) -> Result<(), ProtocolError> {
    // Send MsgInit to transition StInit -> StIdle.
    runner.send(&Message::MsgInit).await?;

    // FIFO of announced tx ids (announced but not yet acked by server).
    let mut announced: VecDeque<PendingTx> = VecDeque::new();
    // Tx ids that have been announced but not yet requested for full body.
    // We keep the full PendingTx so we can look up the body later.
    let mut pending_bodies: VecDeque<PendingTx> = VecDeque::new();

    loop {
        let msg = runner.recv().await?;

        match msg {
            Message::MsgRequestTxIdsBlocking { ack, req } => {
                // Acknowledge the first `ack` announced tx ids.
                for _ in 0..ack {
                    announced.pop_front();
                }

                // Collect available txs from the channel + pending_bodies.
                let mut new_txs: Vec<PendingTx> = Vec::new();

                // Drain any already-buffered pending bodies into new_txs first.
                while new_txs.len() < req as usize {
                    match tx_receiver.try_recv() {
                        Ok(tx) => new_txs.push(tx),
                        Err(_) => break,
                    }
                }

                // If still empty, blocking wait for at least one tx.
                if new_txs.is_empty() {
                    match tx_receiver.recv().await {
                        Some(tx) => new_txs.push(tx),
                        None => {
                            // Channel closed, no more txs — terminate.
                            runner.send(&Message::MsgDone).await?;
                            return Ok(());
                        }
                    }
                    // Try to fill up to req.
                    while new_txs.len() < req as usize {
                        match tx_receiver.try_recv() {
                            Ok(tx) => new_txs.push(tx),
                            Err(_) => break,
                        }
                    }
                }

                let reply: Vec<TxIdAndSize> = new_txs
                    .iter()
                    .map(|tx| TxIdAndSize {
                        tx_id: tx.tx_id.clone(),
                        size: tx.size,
                    })
                    .collect();

                // Track announced txs for body lookups and ack tracking.
                for tx in &new_txs {
                    announced.push_back(tx.clone());
                    pending_bodies.push_back(tx.clone());
                }

                // Drain new_txs (already cloned above).
                drop(new_txs);

                runner
                    .send(&Message::MsgReplyTxIds { tx_ids: reply })
                    .await?;
            }

            Message::MsgRequestTxIdsNonBlocking { ack, req } => {
                // Acknowledge the first `ack` announced tx ids.
                for _ in 0..ack {
                    announced.pop_front();
                }

                // Collect available txs (non-blocking).
                let mut new_txs: Vec<PendingTx> = Vec::new();
                while new_txs.len() < req as usize {
                    match tx_receiver.try_recv() {
                        Ok(tx) => new_txs.push(tx),
                        Err(_) => break,
                    }
                }

                let reply: Vec<TxIdAndSize> = new_txs
                    .iter()
                    .map(|tx| TxIdAndSize {
                        tx_id: tx.tx_id.clone(),
                        size: tx.size,
                    })
                    .collect();

                for tx in &new_txs {
                    announced.push_back(tx.clone());
                    pending_bodies.push_back(tx.clone());
                }

                drop(new_txs);

                runner
                    .send(&Message::MsgReplyTxIds { tx_ids: reply })
                    .await?;
            }

            Message::MsgRequestTxs { tx_ids } => {
                // Look up requested tx bodies from the pending set.
                let mut txs = Vec::new();
                for requested_id in &tx_ids {
                    if let Some(pos) = pending_bodies.iter().position(|p| p.tx_id == *requested_id)
                    {
                        let pending = pending_bodies.remove(pos).expect("position valid");
                        txs.push(pending.body);
                    }
                    // Per spec: omitted txs are treated as never announced.
                }

                runner.send(&Message::MsgReplyTxs { txs }).await?;
            }

            other => {
                return Err(ProtocolError::InvalidMessage(format!(
                    "client received unexpected message: {other:?}"
                )));
            }
        }
    }
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
        assert_eq!(TxSubmission::agency(&State::StInit), Agency::Client);
        assert_eq!(TxSubmission::agency(&State::StIdle), Agency::Server);
        assert_eq!(
            TxSubmission::agency(&State::StTxIdsBlocking),
            Agency::Client
        );
        assert_eq!(
            TxSubmission::agency(&State::StTxIdsNonBlocking),
            Agency::Client
        );
        assert_eq!(TxSubmission::agency(&State::StTxs), Agency::Client);
        assert_eq!(TxSubmission::agency(&State::StDone), Agency::Nobody);
    }

    #[test]
    fn valid_transitions() {
        // StInit -> StIdle
        assert_eq!(
            TxSubmission::transition(&State::StInit, &Message::MsgInit).unwrap(),
            State::StIdle
        );

        // StIdle -> StTxIdsBlocking
        assert_eq!(
            TxSubmission::transition(
                &State::StIdle,
                &Message::MsgRequestTxIdsBlocking { ack: 0, req: 5 }
            )
            .unwrap(),
            State::StTxIdsBlocking
        );

        // StIdle -> StTxIdsNonBlocking
        assert_eq!(
            TxSubmission::transition(
                &State::StIdle,
                &Message::MsgRequestTxIdsNonBlocking { ack: 0, req: 5 }
            )
            .unwrap(),
            State::StTxIdsNonBlocking
        );

        // StIdle -> StTxs
        assert_eq!(
            TxSubmission::transition(
                &State::StIdle,
                &Message::MsgRequestTxs {
                    tx_ids: vec![TxId(vec![0x42])]
                }
            )
            .unwrap(),
            State::StTxs
        );

        // StTxIdsBlocking -> StIdle (reply)
        assert_eq!(
            TxSubmission::transition(
                &State::StTxIdsBlocking,
                &Message::MsgReplyTxIds { tx_ids: vec![] }
            )
            .unwrap(),
            State::StIdle
        );

        // StTxIdsBlocking -> StDone
        assert_eq!(
            TxSubmission::transition(&State::StTxIdsBlocking, &Message::MsgDone).unwrap(),
            State::StDone
        );

        // StTxIdsNonBlocking -> StIdle
        assert_eq!(
            TxSubmission::transition(
                &State::StTxIdsNonBlocking,
                &Message::MsgReplyTxIds { tx_ids: vec![] }
            )
            .unwrap(),
            State::StIdle
        );

        // StTxs -> StIdle
        assert_eq!(
            TxSubmission::transition(&State::StTxs, &Message::MsgReplyTxs { txs: vec![] }).unwrap(),
            State::StIdle
        );
    }

    #[test]
    fn invalid_transitions() {
        // MsgDone only valid in StTxIdsBlocking
        assert!(TxSubmission::transition(&State::StTxIdsNonBlocking, &Message::MsgDone).is_err());
        assert!(TxSubmission::transition(&State::StIdle, &Message::MsgDone).is_err());
        assert!(TxSubmission::transition(&State::StInit, &Message::MsgDone).is_err());

        // MsgInit only valid in StInit
        assert!(TxSubmission::transition(&State::StIdle, &Message::MsgInit).is_err());

        // Server messages not valid in client states
        assert!(TxSubmission::transition(
            &State::StTxIdsBlocking,
            &Message::MsgRequestTxs {
                tx_ids: vec![TxId(vec![])]
            }
        )
        .is_err());
    }

    #[test]
    fn size_limits() {
        assert_eq!(TxSubmission::size_limit(&State::StInit), SIZE_LIMIT_SMALL);
        assert_eq!(TxSubmission::size_limit(&State::StIdle), SIZE_LIMIT_SMALL);
        assert_eq!(
            TxSubmission::size_limit(&State::StTxIdsBlocking),
            SIZE_LIMIT_LARGE
        );
        assert_eq!(
            TxSubmission::size_limit(&State::StTxIdsNonBlocking),
            SIZE_LIMIT_LARGE
        );
        assert_eq!(TxSubmission::size_limit(&State::StTxs), SIZE_LIMIT_LARGE);
    }

    #[test]
    fn timeouts() {
        assert_eq!(TxSubmission::timeout(&State::StInit), None);
        assert_eq!(TxSubmission::timeout(&State::StIdle), None);
        assert_eq!(TxSubmission::timeout(&State::StTxIdsBlocking), None);
        assert_eq!(
            TxSubmission::timeout(&State::StTxIdsNonBlocking),
            Some(TIMEOUT_NON_BLOCKING)
        );
        assert_eq!(TxSubmission::timeout(&State::StTxs), Some(TIMEOUT_TXS));
        assert_eq!(TxSubmission::timeout(&State::StDone), None);
    }

    fn test_config() -> MuxConfig {
        MuxConfig {
            sdu_timeout: std::time::Duration::from_secs(2),
            ..MuxConfig::default()
        }
    }

    fn make_txsubmission_mux_pair() -> (
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

    fn make_test_tx(id_byte: u8, size: usize) -> PendingTx {
        let mut id_buf = Vec::new();
        let mut e = minicbor::Encoder::new(&mut id_buf);
        e.bytes(&[id_byte; 32]).unwrap();

        let mut body_buf = Vec::new();
        let mut e = minicbor::Encoder::new(&mut body_buf);
        e.bytes(&vec![id_byte; size]).unwrap();

        PendingTx {
            tx_id: TxId(id_buf),
            body: TxBody(body_buf),
            size: size as u32,
        }
    }

    #[tokio::test]
    async fn txsubmission_client_server_exchange() {
        let ((cs, cr), (ss, sr), ra, rb) = make_txsubmission_mux_pair();

        let tx1 = make_test_tx(0x01, 1500);
        let tx2 = make_test_tx(0x02, 2000);
        let tx1_id = tx1.tx_id.clone();
        let tx2_id = tx2.tx_id.clone();

        // Server: drive the protocol by requesting tx ids, then txs.
        let server = tokio::spawn(async move {
            let mut runner = Runner::<TxSubmission>::new(Role::Server, ss, sr);

            // Receive MsgInit.
            let msg = runner.recv().await.unwrap();
            assert!(matches!(msg, Message::MsgInit));

            // Request tx ids (blocking), ack 0, request up to 10.
            runner
                .send(&Message::MsgRequestTxIdsBlocking { ack: 0, req: 10 })
                .await
                .unwrap();

            let msg = runner.recv().await.unwrap();
            let announced_ids = match msg {
                Message::MsgReplyTxIds { tx_ids } => {
                    assert_eq!(tx_ids.len(), 2);
                    assert_eq!(tx_ids[0].size, 1500);
                    assert_eq!(tx_ids[1].size, 2000);
                    tx_ids.into_iter().map(|t| t.tx_id).collect::<Vec<_>>()
                }
                other => panic!("expected MsgReplyTxIds, got {other:?}"),
            };

            // Request full transactions.
            runner
                .send(&Message::MsgRequestTxs {
                    tx_ids: announced_ids,
                })
                .await
                .unwrap();

            let msg = runner.recv().await.unwrap();
            match msg {
                Message::MsgReplyTxs { txs } => {
                    assert_eq!(txs.len(), 2);
                }
                other => panic!("expected MsgReplyTxs, got {other:?}"),
            }

            // Ack the 2 txs and request more (blocking). Client should send MsgDone.
            runner
                .send(&Message::MsgRequestTxIdsBlocking { ack: 2, req: 10 })
                .await
                .unwrap();

            let msg = runner.recv().await.unwrap();
            assert!(matches!(msg, Message::MsgDone));
        });

        // Client: use run_client with a channel.
        let client = tokio::spawn(async move {
            let mut runner = Runner::<TxSubmission>::new(Role::Client, cs, cr);
            let (tx_sender, mut tx_receiver) = tokio::sync::mpsc::channel(16);

            // Pre-load txs.
            tx_sender
                .send(PendingTx {
                    tx_id: tx1_id,
                    body: TxBody(tx1.body.0.clone()),
                    size: 1500,
                })
                .await
                .unwrap();
            tx_sender
                .send(PendingTx {
                    tx_id: tx2_id,
                    body: TxBody(tx2.body.0.clone()),
                    size: 2000,
                })
                .await
                .unwrap();
            // Close channel so client knows no more txs.
            drop(tx_sender);

            run_client(&mut runner, &mut tx_receiver).await.unwrap();
        });

        client.await.unwrap();
        server.await.unwrap();
        ra.abort();
        rb.abort();
    }

    #[tokio::test]
    async fn txsubmission_non_blocking_empty_reply() {
        let ((cs, cr), (ss, sr), ra, rb) = make_txsubmission_mux_pair();

        // Server: send non-blocking request, expect empty reply, then blocking
        // request which triggers MsgDone.
        let server = tokio::spawn(async move {
            let mut runner = Runner::<TxSubmission>::new(Role::Server, ss, sr);

            let msg = runner.recv().await.unwrap();
            assert!(matches!(msg, Message::MsgInit));

            // Non-blocking request: no txs available, should get empty reply.
            runner
                .send(&Message::MsgRequestTxIdsNonBlocking { ack: 0, req: 5 })
                .await
                .unwrap();

            let msg = runner.recv().await.unwrap();
            match msg {
                Message::MsgReplyTxIds { tx_ids } => assert!(tx_ids.is_empty()),
                other => panic!("expected empty MsgReplyTxIds, got {other:?}"),
            }

            // Blocking request: channel closed, should get MsgDone.
            runner
                .send(&Message::MsgRequestTxIdsBlocking { ack: 0, req: 5 })
                .await
                .unwrap();

            let msg = runner.recv().await.unwrap();
            assert!(matches!(msg, Message::MsgDone));
        });

        let client = tokio::spawn(async move {
            let mut runner = Runner::<TxSubmission>::new(Role::Client, cs, cr);
            let (_tx_sender, mut tx_receiver) = tokio::sync::mpsc::channel::<PendingTx>(16);
            // Drop sender immediately — no txs to send.
            drop(_tx_sender);

            run_client(&mut runner, &mut tx_receiver).await.unwrap();
        });

        client.await.unwrap();
        server.await.unwrap();
        ra.abort();
        rb.abort();
    }
}
