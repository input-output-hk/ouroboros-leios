//! Server-side protocol handlers for responder peer tasks.
//!
//! Each handler runs one mini-protocol in server (responder) mode,
//! reading from an `Arc<ChainStore>` for chain state and sending
//! events to the coordinator via an `mpsc` channel.

use std::sync::Arc;

use tokio::sync::mpsc;

use crate::types::Point;

use crate::mux::{CodecRecv, CodecSend};
use crate::protocols::blockfetch::{BlockFetch, Message as BfMsg};
use crate::protocols::chainsync::{ChainSync, Message as CsMsg};
use crate::protocols::keepalive::{KeepAlive, Message as KaMsg};
use crate::protocols::leios_fetch::{LeiosFetch, Message as LfMsg};
use crate::protocols::leios_notify::{LeiosNotify, Message as LnMsg};
use crate::protocols::peersharing::{Message as PsMsg, PeerAddress, PeerSharing};
use crate::protocols::txsubmission::{self, Message as TsMsg, TxSubmission};
use crate::protocols::{Role, Runner};

use super::chain_store::ChainStore;
use super::leios_store::LeiosStore;
use super::types::PeerEvent;
use super::PeerId;

/// Serve ChainSync for one connection.
///
/// Responds to intersection queries and streams headers as the chain
/// advances. Uses `ChainStore::subscribe()` to wake when new blocks arrive.
pub async fn serve_chainsync(cs_send: CodecSend, cs_recv: CodecRecv, store: Arc<ChainStore>) {
    let mut runner = Runner::<ChainSync>::new(Role::Server, cs_send, cs_recv);
    let mut read_index: Option<usize> = None;
    let mut subscription = store.subscribe();

    loop {
        let msg = match runner.recv().await {
            Ok(msg) => msg,
            Err(_) => break,
        };

        match msg {
            CsMsg::MsgFindIntersect { points } => match store.find_intersection(&points) {
                Some((point, tip)) => {
                    read_index = store.index_of(&point);
                    let _ = runner.send(&CsMsg::MsgIntersectFound { point, tip }).await;
                }
                None => {
                    let tip = store.tip();
                    let _ = runner.send(&CsMsg::MsgIntersectNotFound { tip }).await;
                }
            },
            CsMsg::MsgRequestNext => {
                // Check if our read pointer was invalidated by a rollback.
                if !store.is_valid_index(read_index) {
                    let tip = store.tip();
                    read_index = store.index_of(&tip.point);
                    let _ = runner
                        .send(&CsMsg::MsgRollBackward {
                            point: tip.point.clone(),
                            tip,
                        })
                        .await;
                } else {
                    let pending = store.blocks_after(read_index);
                    if let Some(block) = pending.first() {
                        read_index = store.index_of(&block.point);
                        let tip = store.tip();
                        let _ = runner
                            .send(&CsMsg::MsgRollForward {
                                header: block.header.clone(),
                                tip,
                            })
                            .await;
                    } else {
                        let _ = runner.send(&CsMsg::MsgAwaitReply).await;

                        loop {
                            if subscription.changed().await.is_err() {
                                return;
                            }
                            // After waking, check for rollback first.
                            if !store.is_valid_index(read_index) {
                                let tip = store.tip();
                                read_index = store.index_of(&tip.point);
                                let _ = runner
                                    .send(&CsMsg::MsgRollBackward {
                                        point: tip.point.clone(),
                                        tip,
                                    })
                                    .await;
                                break;
                            }
                            let pending = store.blocks_after(read_index);
                            if let Some(block) = pending.first() {
                                read_index = store.index_of(&block.point);
                                let tip = store.tip();
                                let _ = runner
                                    .send(&CsMsg::MsgRollForward {
                                        header: block.header.clone(),
                                        tip,
                                    })
                                    .await;
                                break;
                            }
                        }
                    }
                }
            }
            CsMsg::MsgDone => break,
            _ => break,
        }
    }
}

/// Serve BlockFetch for one connection.
///
/// Responds to range requests by streaming blocks from the chain store.
pub async fn serve_blockfetch(bf_send: CodecSend, bf_recv: CodecRecv, store: Arc<ChainStore>) {
    let mut runner = Runner::<BlockFetch>::new(Role::Server, bf_send, bf_recv);

    loop {
        let msg = match runner.recv().await {
            Ok(msg) => msg,
            Err(_) => break,
        };

        match msg {
            BfMsg::MsgRequestRange { from, to } => {
                let blocks = store.get_range(&from, &to);
                if blocks.is_empty() {
                    let _ = runner.send(&BfMsg::MsgNoBlocks).await;
                } else {
                    let _ = runner.send(&BfMsg::MsgStartBatch).await;
                    for block in &blocks {
                        let _ = runner
                            .send(&BfMsg::MsgBlock {
                                body: block.body.clone(),
                            })
                            .await;
                    }
                    let _ = runner.send(&BfMsg::MsgBatchDone).await;
                }
            }
            BfMsg::MsgClientDone => break,
            _ => break,
        }
    }
}

/// Serve KeepAlive for one connection. Stateless echo.
pub async fn serve_keepalive(ka_send: CodecSend, ka_recv: CodecRecv) {
    let mut runner = Runner::<KeepAlive>::new(Role::Server, ka_send, ka_recv);

    loop {
        let msg = match runner.recv().await {
            Ok(msg) => msg,
            Err(_) => break,
        };

        match msg {
            KaMsg::MsgKeepAlive { cookie } => {
                let _ = runner.send(&KaMsg::MsgKeepAliveResponse { cookie }).await;
            }
            KaMsg::MsgDone => break,
            _ => break,
        }
    }
}

/// Serve TxSubmission for one connection (transaction consumer).
///
/// Pulls transactions from the client and forwards them as
/// `PeerEvent::TransactionReceived` to the coordinator.
pub async fn serve_txsubmission(
    ts_send: CodecSend,
    ts_recv: CodecRecv,
    peer_id: PeerId,
    event_sender: mpsc::Sender<(PeerId, PeerEvent)>,
) {
    let mut runner = Runner::<TxSubmission>::new(Role::Server, ts_send, ts_recv);

    // Receive MsgInit.
    let msg = match runner.recv().await {
        Ok(msg) => msg,
        Err(_) => return,
    };
    if !matches!(msg, TsMsg::MsgInit) {
        return;
    }

    let mut outstanding: usize = 0;

    loop {
        let (ack, req) = if outstanding > 0 {
            let ack = outstanding as u16;
            outstanding = 0;
            (ack, txsubmission::MAX_UNACKED as u16)
        } else {
            (0u16, txsubmission::MAX_UNACKED as u16)
        };

        let blocking = outstanding == 0 && ack == 0;
        if blocking {
            runner
                .send(&TsMsg::MsgRequestTxIdsBlocking { ack, req })
                .await
                .ok();
        } else {
            runner
                .send(&TsMsg::MsgRequestTxIdsNonBlocking { ack, req })
                .await
                .ok();
        }

        let msg = match runner.recv().await {
            Ok(msg) => msg,
            Err(_) => break,
        };

        match msg {
            TsMsg::MsgReplyTxIds { tx_ids } => {
                if tx_ids.is_empty() {
                    // Non-blocking empty reply — do a blocking request next.
                    runner
                        .send(&TsMsg::MsgRequestTxIdsBlocking {
                            ack: 0,
                            req: txsubmission::MAX_UNACKED as u16,
                        })
                        .await
                        .ok();

                    let msg = match runner.recv().await {
                        Ok(msg) => msg,
                        Err(_) => break,
                    };

                    match msg {
                        TsMsg::MsgDone => break,
                        TsMsg::MsgReplyTxIds { tx_ids } if !tx_ids.is_empty() => {
                            let ids: Vec<_> = tx_ids.iter().map(|t| t.tx_id.clone()).collect();
                            let count = ids.len();
                            runner
                                .send(&TsMsg::MsgRequestTxs { tx_ids: ids })
                                .await
                                .ok();

                            let msg = match runner.recv().await {
                                Ok(msg) => msg,
                                Err(_) => break,
                            };
                            match msg {
                                TsMsg::MsgReplyTxs { txs } => {
                                    for tx in &txs {
                                        let _ = event_sender
                                            .send((
                                                peer_id,
                                                PeerEvent::TransactionReceived {
                                                    body: tx.0.clone(),
                                                },
                                            ))
                                            .await;
                                    }
                                    outstanding = count;
                                }
                                _ => break,
                            }
                        }
                        _ => break,
                    }
                    continue;
                }

                let ids: Vec<_> = tx_ids.iter().map(|t| t.tx_id.clone()).collect();
                let count = ids.len();
                runner
                    .send(&TsMsg::MsgRequestTxs { tx_ids: ids })
                    .await
                    .ok();

                let msg = match runner.recv().await {
                    Ok(msg) => msg,
                    Err(_) => break,
                };
                match msg {
                    TsMsg::MsgReplyTxs { txs } => {
                        for tx in &txs {
                            let _ = event_sender
                                .send((
                                    peer_id,
                                    PeerEvent::TransactionReceived { body: tx.0.clone() },
                                ))
                                .await;
                        }
                        outstanding = count;
                    }
                    _ => break,
                }
            }
            TsMsg::MsgDone => break,
            _ => break,
        }
    }
}

/// Serve PeerSharing for one connection.
///
/// Uses a callback to provide peer addresses on request.
pub async fn serve_peersharing(
    ps_send: CodecSend,
    ps_recv: CodecRecv,
    peer_provider: Arc<dyn Fn(u8) -> Vec<PeerAddress> + Send + Sync>,
) {
    let mut runner = Runner::<PeerSharing>::new(Role::Server, ps_send, ps_recv);

    loop {
        let msg = match runner.recv().await {
            Ok(msg) => msg,
            Err(_) => break,
        };

        match msg {
            PsMsg::MsgShareRequest { amount } => {
                let peers = peer_provider(amount);
                let _ = runner.send(&PsMsg::MsgSharePeers { peers }).await;
            }
            PsMsg::MsgDone => break,
            _ => break,
        }
    }
}

/// Serve LeiosNotify for one connection.
///
/// Sends notifications about available Leios data as the store is populated.
/// Uses `LeiosStore::subscribe()` to wake when new items are injected.
pub async fn serve_leios_notify(ln_send: CodecSend, ln_recv: CodecRecv, store: Arc<LeiosStore>) {
    use super::leios_store::LeiosNotification;

    let mut runner = Runner::<LeiosNotify>::new(Role::Server, ln_send, ln_recv);
    let mut read_index: usize = 0;
    let mut subscription = store.subscribe();

    loop {
        let msg = match runner.recv().await {
            Ok(msg) => msg,
            Err(_) => break,
        };

        match msg {
            LnMsg::MsgLeiosNotificationRequestNext => {
                let pending = store.notifications_after(read_index);
                if let Some(notification) = pending.first() {
                    read_index += 1;
                    let response = match notification {
                        LeiosNotification::BlockOffer { point } => LnMsg::MsgLeiosBlockOffer {
                            point: point.clone(),
                        },
                        LeiosNotification::BlockTxsOffer { point } => {
                            LnMsg::MsgLeiosBlockTxsOffer {
                                point: point.clone(),
                            }
                        }
                        LeiosNotification::VotesOffer { votes } => LnMsg::MsgLeiosVotesOffer {
                            votes: votes.clone(),
                        },
                    };
                    if runner.send(&response).await.is_err() {
                        break;
                    }
                } else {
                    // No pending notifications — wait for new items.
                    loop {
                        if subscription.changed().await.is_err() {
                            return;
                        }
                        let pending = store.notifications_after(read_index);
                        if let Some(notification) = pending.first() {
                            read_index += 1;
                            let response = match notification {
                                LeiosNotification::BlockOffer { point } => {
                                    LnMsg::MsgLeiosBlockOffer {
                                        point: point.clone(),
                                    }
                                }
                                LeiosNotification::BlockTxsOffer { point } => {
                                    LnMsg::MsgLeiosBlockTxsOffer {
                                        point: point.clone(),
                                    }
                                }
                                LeiosNotification::VotesOffer { votes } => {
                                    LnMsg::MsgLeiosVotesOffer {
                                        votes: votes.clone(),
                                    }
                                }
                            };
                            if runner.send(&response).await.is_err() {
                                return;
                            }
                            break;
                        }
                    }
                }
            }
            LnMsg::MsgDone => break,
            _ => break,
        }
    }
}

/// Serve LeiosFetch for one connection.
///
/// Responds to block and vote fetch requests from the Leios store.
pub async fn serve_leios_fetch(lf_send: CodecSend, lf_recv: CodecRecv, store: Arc<LeiosStore>) {
    let mut runner = Runner::<LeiosFetch>::new(Role::Server, lf_send, lf_recv);

    loop {
        let msg = match runner.recv().await {
            Ok(msg) => msg,
            Err(_) => break,
        };

        match msg {
            LfMsg::MsgLeiosBlockRequest { point } => {
                let block = match &point {
                    Point::Specific { slot, hash } => {
                        store.get_block(*slot, hash).unwrap_or_default()
                    }
                    Point::Origin => Vec::new(),
                };
                if runner.send(&LfMsg::MsgLeiosBlock { block }).await.is_err() {
                    break;
                }
            }
            LfMsg::MsgLeiosBlockTxsRequest {
                point,
                bitmap: _,
            } => {
                let transactions = match &point {
                    Point::Specific { slot, hash } => {
                        store.get_block_txs(*slot, hash).unwrap_or_default()
                    }
                    Point::Origin => Vec::new(),
                };
                if runner
                    .send(&LfMsg::MsgLeiosBlockTxs { transactions })
                    .await
                    .is_err()
                {
                    break;
                }
            }
            LfMsg::MsgLeiosVotesRequest { votes: ids } => {
                let votes = store.get_votes(&ids);
                if runner
                    .send(&LfMsg::MsgLeiosVoteDelivery { votes })
                    .await
                    .is_err()
                {
                    break;
                }
            }
            LfMsg::MsgDone => break,
            _ => break,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bearer::mem::MemBearer;
    use crate::mux::scheduler::RoundRobin;
    use crate::mux::{Mux, MuxConfig, ProtocolConfig, MODE_INITIATOR, MODE_RESPONDER};
    use crate::protocols::blockfetch;
    use crate::protocols::chainsync;
    use crate::protocols::keepalive;
    use crate::protocols::leios_fetch::{self, LeiosFetch};
    use crate::protocols::leios_notify::{self, LeiosNotify};
    use crate::types::{BlockBody, Point, WrappedHeader};

    fn make_point(slot: u64) -> Point {
        Point::Specific {
            slot,
            hash: [slot as u8; 32],
        }
    }

    /// Create a valid CBOR-encoded WrappedHeader for testing.
    /// Uses CBOR: array(1, unsigned(slot)) = [slot].
    fn make_header(slot: u64) -> WrappedHeader {
        let mut buf = Vec::new();
        minicbor::encode(&[slot], &mut buf).unwrap();
        WrappedHeader::opaque(buf)
    }

    /// Create a valid CBOR-encoded BlockBody for testing.
    /// Uses CBOR: array(1, unsigned(slot)) = [slot], padded to `size` isn't
    /// needed — we just need valid CBOR that's distinguishable per slot.
    fn make_body(slot: u64, _size: usize) -> BlockBody {
        let mut buf = Vec::new();
        minicbor::encode(&[slot], &mut buf).unwrap();
        BlockBody::opaque(buf)
    }

    /// Helper: set up a mux pair for a single protocol.
    fn mux_pair_for_protocol(
        proto: &ProtocolConfig,
    ) -> (
        (CodecSend, CodecRecv),
        (CodecSend, CodecRecv),
        crate::mux::RunningMux,
        crate::mux::RunningMux,
    ) {
        let (bearer_a, bearer_b) = MemBearer::pair();
        let mut mux_a = Mux::new(MuxConfig::default(), RoundRobin::default(), MODE_INITIATOR);
        let (send_a, recv_a) = mux_a.register(proto);
        let running_a = mux_a.run(bearer_a);

        let mut mux_b = Mux::new(MuxConfig::default(), RoundRobin::default(), MODE_RESPONDER);
        let (send_b, recv_b) = mux_b.register(proto);
        let running_b = mux_b.run(bearer_b);

        (
            (CodecSend::new(send_a), CodecRecv::new(recv_a)),
            (CodecSend::new(send_b), CodecRecv::new(recv_b)),
            running_a,
            running_b,
        )
    }

    #[tokio::test]
    async fn chainsync_server_responds_to_intersection_and_roll_forward() {
        let cs_proto = ProtocolConfig {
            id: chainsync::PROTOCOL_ID,
            priority: 1,
            ingress_limit: chainsync::INGRESS_LIMIT,
            egress_queue_size: 16,
        };

        let ((client_send, client_recv), (server_send, server_recv), mux_a, mux_b) =
            mux_pair_for_protocol(&cs_proto);

        // Populate chain store.
        let (store, _rx) = ChainStore::new(100);
        let header_1 = make_header(1);
        for slot in 1..=3 {
            store.append_block(make_point(slot), make_header(slot), make_body(slot, 50));
        }

        // Start server.
        let server_handle = tokio::spawn(serve_chainsync(server_send, server_recv, store));

        // Client: find intersection at Origin.
        let mut client = Runner::<ChainSync>::new(Role::Client, client_send, client_recv);
        let result = chainsync::find_intersection(&mut client, vec![Point::Origin]).await;
        assert!(result.is_ok());
        let (point, tip) = result.unwrap().unwrap();
        assert_eq!(point, Point::Origin);
        assert_eq!(tip.block_no, 3);

        // Client: request next → should get block 1.
        let event = chainsync::request_next(&mut client).await.unwrap();
        match event {
            chainsync::ChainSyncEvent::RollForward { header, tip } => {
                assert_eq!(header.raw, header_1.raw);
                assert_eq!(tip.block_no, 3);
            }
            other => panic!("expected RollForward, got {other:?}"),
        }

        // Clean up.
        let _ = chainsync::done(&mut client).await;
        server_handle.await.ok();
        mux_a.abort();
        mux_b.abort();
    }

    #[tokio::test]
    async fn blockfetch_server_streams_blocks() {
        let bf_proto = ProtocolConfig {
            id: blockfetch::PROTOCOL_ID,
            priority: 2,
            ingress_limit: blockfetch::INGRESS_LIMIT,
            egress_queue_size: 16,
        };

        let ((client_send, client_recv), (server_send, server_recv), mux_a, mux_b) =
            mux_pair_for_protocol(&bf_proto);

        let (store, _rx) = ChainStore::new(100);
        let body_1 = make_body(1, 100);
        let body_3 = make_body(3, 100);
        for slot in 1..=3 {
            store.append_block(make_point(slot), make_header(slot), make_body(slot, 100));
        }

        let server_handle = tokio::spawn(serve_blockfetch(server_send, server_recv, store));

        let mut client = Runner::<BlockFetch>::new(Role::Client, client_send, client_recv);

        // Request range [1..3].
        let has_blocks = blockfetch::request_range(&mut client, make_point(1), make_point(3)).await;
        assert!(has_blocks.unwrap());

        // Receive 3 blocks.
        let mut received = Vec::new();
        while let Ok(Some(body)) = blockfetch::recv_block(&mut client).await {
            received.push(body);
        }
        assert_eq!(received.len(), 3);
        assert_eq!(received[0].raw, body_1.raw);
        assert_eq!(received[2].raw, body_3.raw);

        let _ = blockfetch::done(&mut client).await;
        server_handle.await.ok();
        mux_a.abort();
        mux_b.abort();
    }

    #[tokio::test]
    async fn keepalive_server_echoes_cookie() {
        let ka_proto = ProtocolConfig {
            id: keepalive::PROTOCOL_ID,
            priority: 7,
            ingress_limit: keepalive::INGRESS_LIMIT,
            egress_queue_size: 4,
        };

        let ((client_send, client_recv), (server_send, server_recv), mux_a, mux_b) =
            mux_pair_for_protocol(&ka_proto);

        let server_handle = tokio::spawn(serve_keepalive(server_send, server_recv));

        let mut client = Runner::<KeepAlive>::new(Role::Client, client_send, client_recv);
        let rtt = keepalive::keep_alive(&mut client, 42).await.unwrap();
        assert!(rtt.as_millis() < 1000); // MemBearer should be fast

        let _ = keepalive::done(&mut client).await;
        server_handle.await.ok();
        mux_a.abort();
        mux_b.abort();
    }

    #[tokio::test]
    async fn leios_notify_server_sends_notifications() {
        let ln_proto = ProtocolConfig {
            id: leios_notify::PROTOCOL_ID,
            priority: 0,
            ingress_limit: leios_notify::INGRESS_LIMIT,
            egress_queue_size: 16,
        };

        let ((client_send, client_recv), (server_send, server_recv), mux_a, mux_b) =
            mux_pair_for_protocol(&ln_proto);

        // Create and populate LeiosStore.
        let (store, _rx) = LeiosStore::new(100);
        store.inject_block(
            Point::Specific {
                slot: 42,
                hash: [0xAB; 32],
            },
            vec![1, 2, 3],
        );

        // Start server.
        let server_handle = tokio::spawn(serve_leios_notify(server_send, server_recv, store));

        // Client: request next notification.
        let mut client = Runner::<LeiosNotify>::new(Role::Client, client_send, client_recv);
        let event = leios_notify::request_next(&mut client).await.unwrap();
        match event {
            leios_notify::LeiosNotifyEvent::BlockOffer { point } => {
                assert_eq!(
                    point,
                    Point::Specific {
                        slot: 42,
                        hash: [0xAB; 32]
                    }
                );
            }
            other => panic!("expected BlockOffer, got {other:?}"),
        }

        // Clean up.
        let _ = leios_notify::done(&mut client).await;
        server_handle.await.ok();
        mux_a.abort();
        mux_b.abort();
    }

    #[tokio::test]
    async fn leios_fetch_server_delivers_block() {
        let lf_proto = ProtocolConfig {
            id: leios_fetch::PROTOCOL_ID,
            priority: 0,
            ingress_limit: leios_fetch::INGRESS_LIMIT,
            egress_queue_size: 16,
        };

        let ((client_send, client_recv), (server_send, server_recv), mux_a, mux_b) =
            mux_pair_for_protocol(&lf_proto);

        // Create and populate LeiosStore.
        let (store, _rx) = LeiosStore::new(100);
        store.inject_block(
            Point::Specific {
                slot: 42,
                hash: [0xAB; 32],
            },
            vec![1, 2, 3, 4],
        );

        // Start server.
        let server_handle = tokio::spawn(serve_leios_fetch(server_send, server_recv, store));

        // Client: fetch block.
        let mut client = Runner::<LeiosFetch>::new(Role::Client, client_send, client_recv);
        let block = leios_fetch::fetch_block(&mut client, Point::Specific { slot: 42, hash: [0xAB; 32] })
            .await
            .unwrap();
        assert_eq!(block, vec![1, 2, 3, 4]);

        // Clean up.
        let _ = leios_fetch::done(&mut client).await;
        server_handle.await.ok();
        mux_a.abort();
        mux_b.abort();
    }
}
