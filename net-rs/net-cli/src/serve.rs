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
use net_core::protocols::blockfetch::{BlockFetch, BlockFetchRequest, BlockFetchResponse};
use net_core::protocols::chainsync;
use net_core::protocols::chainsync::{ChainSync, ChainSyncRequest, ChainSyncResponse};
use net_core::protocols::keepalive;
use net_core::protocols::keepalive::{KeepAlive, KeepAliveRequest, KeepAliveResponse};
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
}

/// Background task that generates blocks on a Poisson schedule.
async fn block_generator(chain: FakeChain, notify: watch::Sender<u64>, rate: f64) {
    let mut rng = StdRng::from_entropy();

    loop {
        // Exponential inter-arrival time: -ln(U) / λ
        let u: f64 = rng.gen_range(0.001..1.0);
        let interval = Duration::from_secs_f64(-u.ln() / rate);
        tokio::time::sleep(interval).await;

        let block = {
            let mut inner = chain.inner.lock().unwrap();
            let slot = inner.next_slot;
            inner.next_slot += 1;

            let mut hash = [0u8; 32];
            rng.fill(&mut hash);

            let point = Point::Specific { slot, hash };

            // Opaque dummy header and body — must be valid CBOR.
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

/// Serve ChainSync for one connection.
async fn serve_chainsync(cs_send: CodecSend, cs_recv: CodecRecv, chain: FakeChain) {
    let mut runner = Runner::<ChainSync>::new(Role::Server, cs_send, cs_recv);
    let mut read_index: Option<usize> = None; // None = before first block (Origin)
    let mut subscription = chain.subscribe();

    loop {
        let req = match chainsync::receive_request(&mut runner).await {
            Ok(req) => req,
            Err(_) => break,
        };

        match req {
            ChainSyncRequest::FindIntersect(points) => match chain.find_intersection(&points) {
                Some((point, tip)) => {
                    read_index = chain.index_of(&point);
                    let _ = chainsync::send_response(
                        &mut runner,
                        ChainSyncResponse::IntersectFound { point, tip },
                    )
                    .await;
                }
                None => {
                    let tip = chain.tip();
                    let _ = chainsync::send_response(
                        &mut runner,
                        ChainSyncResponse::IntersectNotFound { tip },
                    )
                    .await;
                }
            },
            ChainSyncRequest::RequestNext => {
                // Check if there are blocks after our read pointer.
                let pending = chain.blocks_after(read_index);
                if let Some(block) = pending.first() {
                    read_index = chain.index_of(&block.point);
                    let tip = chain.tip();
                    let _ = chainsync::send_response(
                        &mut runner,
                        ChainSyncResponse::RollForward {
                            header: block.header.clone(),
                            tip,
                        },
                    )
                    .await;
                } else {
                    // At tip — send AwaitReply and wait for a new block.
                    let _ =
                        chainsync::send_response(&mut runner, ChainSyncResponse::AwaitReply).await;

                    // Wait until a new block is actually available.
                    loop {
                        if subscription.changed().await.is_err() {
                            return; // chain shut down
                        }
                        let pending = chain.blocks_after(read_index);
                        if let Some(block) = pending.first() {
                            read_index = chain.index_of(&block.point);
                            let tip = chain.tip();
                            let _ = chainsync::send_response(
                                &mut runner,
                                ChainSyncResponse::RollForward {
                                    header: block.header.clone(),
                                    tip,
                                },
                            )
                            .await;
                            break;
                        }
                    }
                }
            }
            ChainSyncRequest::Done => break,
        }
    }
}

/// Serve BlockFetch for one connection.
async fn serve_blockfetch(bf_send: CodecSend, bf_recv: CodecRecv, chain: FakeChain) {
    let mut runner = Runner::<BlockFetch>::new(Role::Server, bf_send, bf_recv);

    loop {
        let req = match blockfetch::receive_request(&mut runner).await {
            Ok(req) => req,
            Err(_) => break,
        };

        match req {
            BlockFetchRequest::RequestRange { from, to } => {
                let blocks = chain.get_range(&from, &to);
                if blocks.is_empty() {
                    let _ =
                        blockfetch::send_response(&mut runner, BlockFetchResponse::NoBlocks).await;
                } else {
                    let _ = blockfetch::send_response(&mut runner, BlockFetchResponse::StartBatch)
                        .await;
                    for block in &blocks {
                        let _ = blockfetch::send_response(
                            &mut runner,
                            BlockFetchResponse::Block {
                                body: block.body.clone(),
                            },
                        )
                        .await;
                    }
                    let _ =
                        blockfetch::send_response(&mut runner, BlockFetchResponse::BatchDone).await;
                }
            }
            BlockFetchRequest::ClientDone => break,
        }
    }
}

/// Serve KeepAlive for one connection.
async fn serve_keepalive(ka_send: CodecSend, ka_recv: CodecRecv) {
    let mut runner = Runner::<KeepAlive>::new(Role::Server, ka_send, ka_recv);

    loop {
        let req = match keepalive::receive_request(&mut runner).await {
            Ok(req) => req,
            Err(_) => break,
        };

        match req {
            KeepAliveRequest::KeepAlive { cookie } => {
                let _ = keepalive::send_response(
                    &mut runner,
                    KeepAliveResponse::KeepAliveResponse { cookie },
                )
                .await;
            }
            KeepAliveRequest::Done => break,
        }
    }
}

pub async fn run(port: u16, magic: u64, block_rate: f64) -> Result<(), Box<dyn std::error::Error>> {
    let (chain, notify) = FakeChain::new();

    // Start block generator.
    let chain_gen = chain.clone();
    tokio::spawn(async move {
        block_generator(chain_gen, notify, block_rate).await;
    });

    println!(
        "fake server listening on port {port} (magic={magic}, rate={block_rate} blocks/sec, ~{:.0}s mean interval)",
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
            &[cs_proto.clone(), bf_proto.clone(), ka_proto.clone()],
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
            let (ka_send, ka_recv) = channels.next().expect("keepalive channel");

            // Run all protocols concurrently. ChainSync is the primary —
            // when it finishes (client Done or error), we clean up.
            let bf_handle = tokio::spawn(serve_blockfetch(bf_send, bf_recv, chain.clone()));
            let ka_handle = tokio::spawn(serve_keepalive(ka_send, ka_recv));

            serve_chainsync(cs_send, cs_recv, chain).await;

            bf_handle.abort();
            ka_handle.abort();
            conn.running.abort();
            println!("  client disconnected");
        });
    }
}
