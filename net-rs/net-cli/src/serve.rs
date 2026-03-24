//! Fake Cardano node server: accepts connections and serves a synthetic
//! block chain generated on a Poisson distribution.

use std::sync::{Arc, Mutex};
use std::time::Duration;

use rand::rngs::StdRng;
use rand::{Rng, SeedableRng};
use tokio::net::TcpListener;
use tokio::sync::watch;

use net_core::codec::{CodecRecv, CodecSend};
use net_core::mux::{MuxConfig, ProtocolConfig};
use net_core::protocol::Role;
use net_core::protocol::Runner;
use net_core::protocols::blockfetch;
use net_core::protocols::blockfetch::{BlockFetch, Message as BfMsg};
use net_core::protocols::chainsync;
use net_core::protocols::chainsync::{ChainSync, Message as CsMsg};
use net_core::protocols::keepalive;
use net_core::protocols::keepalive::{KeepAlive, Message as KaMsg};
use net_core::protocols::peersharing;
use net_core::protocols::peersharing::{Message as PsMsg, PeerAddress, PeerSharing};
use net_core::protocols::txsubmission;
use net_core::protocols::txsubmission::{Message as TsMsg, TxSubmission};
use net_core::types::{BlockBody, Point, Tip, WrappedHeader};

use crate::connect;

/// A single block in the fake chain.
#[derive(Clone)]
struct FakeBlock {
    point: Point,
    header: WrappedHeader,
    body: BlockBody,
}

/// Shared fake chain state.
struct FakeChainInner {
    blocks: Vec<FakeBlock>,
    next_slot: u64,
}

/// Thread-safe handle to the fake chain.
#[derive(Clone)]
struct FakeChain {
    inner: Arc<Mutex<FakeChainInner>>,
    notify: watch::Receiver<u64>, // block count
}

impl FakeChain {
    fn new() -> (Self, watch::Sender<u64>) {
        let (tx, rx) = watch::channel(0u64);
        let chain = FakeChain {
            inner: Arc::new(Mutex::new(FakeChainInner {
                blocks: Vec::new(),
                next_slot: 1,
            })),
            notify: rx,
        };
        (chain, tx)
    }

    fn tip(&self) -> Tip {
        let inner = self.inner.lock().unwrap();
        match inner.blocks.last() {
            Some(block) => Tip {
                point: block.point.clone(),
                block_no: inner.blocks.len() as u64,
            },
            None => Tip {
                point: Point::Origin,
                block_no: 0,
            },
        }
    }

    fn find_intersection(&self, points: &[Point]) -> Option<(Point, Tip)> {
        let inner = self.inner.lock().unwrap();
        let tip = match inner.blocks.last() {
            Some(block) => Tip {
                point: block.point.clone(),
                block_no: inner.blocks.len() as u64,
            },
            None => Tip {
                point: Point::Origin,
                block_no: 0,
            },
        };

        for candidate in points {
            if *candidate == Point::Origin {
                return Some((Point::Origin, tip));
            }
            if inner.blocks.iter().any(|b| b.point == *candidate) {
                return Some((candidate.clone(), tip));
            }
        }
        None
    }

    /// Get the index of a point in the chain. Returns None for Origin (before first block).
    fn index_of(&self, point: &Point) -> Option<usize> {
        let inner = self.inner.lock().unwrap();
        if *point == Point::Origin {
            return None;
        }
        inner.blocks.iter().position(|b| b.point == *point)
    }

    /// Get blocks after the given index (exclusive).
    fn blocks_after(&self, after_index: Option<usize>) -> Vec<FakeBlock> {
        let inner = self.inner.lock().unwrap();
        let start = match after_index {
            Some(i) => i + 1,
            None => 0, // Origin — start from beginning
        };
        inner.blocks[start..].to_vec()
    }

    /// Get blocks in a range (inclusive on both ends).
    fn get_range(&self, from: &Point, to: &Point) -> Vec<FakeBlock> {
        let inner = self.inner.lock().unwrap();
        let start = inner.blocks.iter().position(|b| b.point == *from);
        let end = inner.blocks.iter().position(|b| b.point == *to);
        match (start, end) {
            (Some(s), Some(e)) if s <= e => inner.blocks[s..=e].to_vec(),
            _ => Vec::new(),
        }
    }

    /// Subscribe to new block notifications.
    fn subscribe(&self) -> watch::Receiver<u64> {
        self.notify.clone()
    }

    fn block_count(&self) -> u64 {
        self.inner.lock().unwrap().blocks.len() as u64
    }

    /// Roll back the chain by `depth` blocks. Returns the new tip point.
    fn rollback(&self, depth: usize) -> Point {
        let mut inner = self.inner.lock().unwrap();
        let new_len = inner.blocks.len().saturating_sub(depth);
        inner.blocks.truncate(new_len);
        match inner.blocks.last() {
            Some(block) => block.point.clone(),
            None => Point::Origin,
        }
    }

    /// Check if the given read_index is still valid (within the chain).
    fn is_valid_index(&self, index: Option<usize>) -> bool {
        let inner = self.inner.lock().unwrap();
        match index {
            None => true, // Origin is always valid
            Some(i) => i < inner.blocks.len(),
        }
    }
}

/// Sample an exponential inter-arrival time: -ln(U) / λ
fn exp_sample(rng: &mut StdRng, rate: f64) -> Duration {
    let u: f64 = rng.gen_range(0.001..1.0);
    Duration::from_secs_f64(-u.ln() / rate)
}

/// Background task that generates blocks and occasional rollbacks on Poisson schedules.
async fn block_generator(
    chain: FakeChain,
    notify: watch::Sender<u64>,
    block_rate: f64,
    rollback_rate: f64,
    max_rollback_depth: usize,
) {
    let mut rng = StdRng::from_entropy();

    loop {
        // Sample next event: block or rollback, whichever comes first.
        let block_interval = exp_sample(&mut rng, block_rate);
        let rollback_interval = if rollback_rate > 0.0 {
            exp_sample(&mut rng, rollback_rate)
        } else {
            Duration::from_secs(u64::MAX) // effectively never
        };

        if rollback_interval < block_interval && chain.block_count() > 1 {
            tokio::time::sleep(rollback_interval).await;

            let max_depth = (chain.block_count() as usize - 1).min(max_rollback_depth);
            let depth = rng.gen_range(1..=max_depth);
            let new_tip = chain.rollback(depth);
            let count = chain.block_count();
            println!("  rollback depth={depth}, new tip: {new_tip} (#{count})");
            let _ = notify.send(count);
        } else {
            tokio::time::sleep(block_interval).await;

            let block = {
                let mut inner = chain.inner.lock().unwrap();
                let slot = inner.next_slot;
                inner.next_slot += 1;

                let mut hash = [0u8; 32];
                rng.fill(&mut hash);

                let point = Point::Specific { slot, hash };

                let mut cbor_buf = Vec::new();
                let mut enc = minicbor::Encoder::new(&mut cbor_buf);
                enc.bytes(&hash).expect("CBOR encode");
                let header = WrappedHeader(cbor_buf.clone());
                let body = BlockBody(cbor_buf);

                let block = FakeBlock {
                    point,
                    header,
                    body,
                };
                inner.blocks.push(block.clone());
                block
            };

            let count = chain.block_count();
            println!("  generated block #{count} at slot {}", block.point);
            let _ = notify.send(count);
        }
    }
}

/// Serve ChainSync for one connection.
async fn serve_chainsync(cs_send: CodecSend, cs_recv: CodecRecv, chain: FakeChain) {
    let mut runner = Runner::<ChainSync>::new(Role::Server, cs_send, cs_recv);
    let mut read_index: Option<usize> = None; // None = before first block (Origin)
    let mut subscription = chain.subscribe();

    loop {
        let msg = match runner.recv().await {
            Ok(msg) => msg,
            Err(_) => break,
        };

        match msg {
            CsMsg::MsgFindIntersect { points } => match chain.find_intersection(&points) {
                Some((point, tip)) => {
                    read_index = chain.index_of(&point);
                    let _ = runner.send(&CsMsg::MsgIntersectFound { point, tip }).await;
                }
                None => {
                    let tip = chain.tip();
                    let _ = runner.send(&CsMsg::MsgIntersectNotFound { tip }).await;
                }
            },
            CsMsg::MsgRequestNext => {
                // Check if our read pointer was invalidated by a rollback.
                if !chain.is_valid_index(read_index) {
                    let tip = chain.tip();
                    read_index = chain.index_of(&tip.point);
                    let _ = runner
                        .send(&CsMsg::MsgRollBackward {
                            point: tip.point.clone(),
                            tip,
                        })
                        .await;
                } else {
                    let pending = chain.blocks_after(read_index);
                    if let Some(block) = pending.first() {
                        read_index = chain.index_of(&block.point);
                        let tip = chain.tip();
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
                            if !chain.is_valid_index(read_index) {
                                let tip = chain.tip();
                                read_index = chain.index_of(&tip.point);
                                let _ = runner
                                    .send(&CsMsg::MsgRollBackward {
                                        point: tip.point.clone(),
                                        tip,
                                    })
                                    .await;
                                break;
                            }
                            let pending = chain.blocks_after(read_index);
                            if let Some(block) = pending.first() {
                                read_index = chain.index_of(&block.point);
                                let tip = chain.tip();
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
async fn serve_blockfetch(bf_send: CodecSend, bf_recv: CodecRecv, chain: FakeChain) {
    let mut runner = Runner::<BlockFetch>::new(Role::Server, bf_send, bf_recv);

    loop {
        let msg = match runner.recv().await {
            Ok(msg) => msg,
            Err(_) => break,
        };

        match msg {
            BfMsg::MsgRequestRange { from, to } => {
                let blocks = chain.get_range(&from, &to);
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

/// Serve KeepAlive for one connection.
async fn serve_keepalive(ka_send: CodecSend, ka_recv: CodecRecv) {
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

/// Serve PeerSharing for one connection (returns fake peers).
async fn serve_peersharing(ps_send: CodecSend, ps_recv: CodecRecv) {
    use std::net::Ipv4Addr;

    let mut runner = Runner::<PeerSharing>::new(Role::Server, ps_send, ps_recv);

    let fake_peers = [
        PeerAddress::IPv4 {
            addr: Ipv4Addr::new(192, 0, 2, 1),
            port: 3001,
        },
        PeerAddress::IPv4 {
            addr: Ipv4Addr::new(192, 0, 2, 2),
            port: 3001,
        },
        PeerAddress::IPv4 {
            addr: Ipv4Addr::new(192, 0, 2, 3),
            port: 3001,
        },
    ];

    loop {
        let msg = match runner.recv().await {
            Ok(msg) => msg,
            Err(_) => break,
        };

        match msg {
            PsMsg::MsgShareRequest { amount } => {
                let count = (amount as usize).min(fake_peers.len());
                let peers = fake_peers[..count].to_vec();
                println!("  peersharing: sharing {count} peer(s)");
                let _ = runner.send(&PsMsg::MsgSharePeers { peers }).await;
            }
            PsMsg::MsgDone => break,
            _ => break,
        }
    }
}

/// Serve TxSubmission for one connection (transaction consumer).
async fn serve_txsubmission(ts_send: CodecSend, ts_recv: CodecRecv) {
    let mut runner = Runner::<TxSubmission>::new(Role::Server, ts_send, ts_recv);

    // Receive MsgInit.
    let msg = match runner.recv().await {
        Ok(msg) => msg,
        Err(_) => return,
    };
    if !matches!(msg, TsMsg::MsgInit) {
        return;
    }

    let mut outstanding: usize = 0; // number of announced but unacked tx ids

    loop {
        // Decide whether to send a blocking or non-blocking request.
        let (ack, req) = if outstanding > 0 {
            // We have outstanding ids — use non-blocking to check for more,
            // and ack what we've consumed.
            let ack = outstanding as u16;
            outstanding = 0;
            (ack, txsubmission::MAX_UNACKED as u16)
        } else {
            // Nothing outstanding — blocking wait for at least one tx.
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
                        TsMsg::MsgDone => {
                            println!("  txsubmission: client done");
                            break;
                        }
                        TsMsg::MsgReplyTxIds { tx_ids } if !tx_ids.is_empty() => {
                            // Request the full transactions.
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
                                    println!(
                                        "  txsubmission: received {} tx(s), {} bytes total",
                                        txs.len(),
                                        txs.iter().map(|t| t.0.len()).sum::<usize>()
                                    );
                                    outstanding = count;
                                }
                                _ => break,
                            }
                        }
                        _ => break,
                    }
                    continue;
                }

                // Got some tx ids — request the full transactions.
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
                        println!(
                            "  txsubmission: received {} tx(s), {} bytes total",
                            txs.len(),
                            txs.iter().map(|t| t.0.len()).sum::<usize>()
                        );
                        outstanding = count;
                    }
                    _ => break,
                }
            }
            TsMsg::MsgDone => {
                println!("  txsubmission: client done");
                break;
            }
            _ => break,
        }
    }
}

pub async fn run(
    port: u16,
    magic: u64,
    block_rate: f64,
    rollback_rate: f64,
    max_rollback_depth: usize,
) -> Result<(), Box<dyn std::error::Error>> {
    let (chain, notify) = FakeChain::new();

    // Start block generator.
    let chain_gen = chain.clone();
    tokio::spawn(async move {
        block_generator(
            chain_gen,
            notify,
            block_rate,
            rollback_rate,
            max_rollback_depth,
        )
        .await;
    });

    let rollback_info = if rollback_rate > 0.0 {
        format!(", rollback rate={rollback_rate}/sec")
    } else {
        String::new()
    };
    println!(
        "fake server listening on port {port} (magic={magic}, block rate={block_rate}/sec (~{:.0}s mean){rollback_info})",
        1.0 / block_rate
    );

    let listener = TcpListener::bind(format!("0.0.0.0:{port}")).await?;

    let cs_proto = ProtocolConfig {
        id: chainsync::PROTOCOL_ID,
        priority: 1,
        ingress_limit: chainsync::INGRESS_LIMIT,
        egress_queue_size: 16,
    };
    let bf_proto = ProtocolConfig {
        id: blockfetch::PROTOCOL_ID,
        priority: 2,
        ingress_limit: blockfetch::INGRESS_LIMIT,
        egress_queue_size: 16,
    };
    let ts_proto = ProtocolConfig {
        id: txsubmission::PROTOCOL_ID,
        priority: 3,
        ingress_limit: txsubmission::INGRESS_LIMIT,
        egress_queue_size: 16,
    };
    let ps_proto = ProtocolConfig {
        id: peersharing::PROTOCOL_ID,
        priority: 5,
        ingress_limit: peersharing::INGRESS_LIMIT,
        egress_queue_size: 4,
    };
    let ka_proto = ProtocolConfig {
        id: keepalive::PROTOCOL_ID,
        priority: 7,
        ingress_limit: keepalive::INGRESS_LIMIT,
        egress_queue_size: 4,
    };

    let mux_config = MuxConfig {
        sdu_timeout: Duration::from_secs(900),
        ..MuxConfig::default()
    };

    loop {
        let conn = match connect::accept_and_handshake(
            &listener,
            magic,
            &[
                cs_proto.clone(),
                bf_proto.clone(),
                ts_proto.clone(),
                ps_proto.clone(),
                ka_proto.clone(),
            ],
            mux_config.clone(),
        )
        .await
        {
            Ok(conn) => conn,
            Err(e) => {
                println!("  handshake failed: {e}");
                continue;
            }
        };

        let chain = chain.clone();

        tokio::spawn(async move {
            let mut channels = conn.channels.into_iter();
            let (cs_send, cs_recv) = channels.next().expect("chainsync channel");
            let (bf_send, bf_recv) = channels.next().expect("blockfetch channel");
            let (ts_send, ts_recv) = channels.next().expect("txsubmission channel");
            let (ps_send, ps_recv) = channels.next().expect("peersharing channel");
            let (ka_send, ka_recv) = channels.next().expect("keepalive channel");

            // Run all protocols concurrently. ChainSync is the primary —
            // when it finishes (client Done or error), we clean up.
            let bf_handle = tokio::spawn(serve_blockfetch(bf_send, bf_recv, chain.clone()));
            let ts_handle = tokio::spawn(serve_txsubmission(ts_send, ts_recv));
            let ps_handle = tokio::spawn(serve_peersharing(ps_send, ps_recv));
            let ka_handle = tokio::spawn(serve_keepalive(ka_send, ka_recv));

            serve_chainsync(cs_send, cs_recv, chain).await;

            bf_handle.abort();
            ts_handle.abort();
            ps_handle.abort();
            ka_handle.abort();
            conn.running.abort();
            println!("  client disconnected");
        });
    }
}
