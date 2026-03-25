//! Persistent chain follower: connects to a node and follows the tip
//! indefinitely, reconnecting on failure. Runs KeepAlive in the background
//! to prevent the peer from dropping the connection.

use std::collections::VecDeque;
use std::time::{Duration, Instant};

use net_core::mux::{MuxConfig, ProtocolConfig};
use net_core::protocols::chainsync;
use net_core::protocols::chainsync::{ChainSync, ChainSyncEvent};
use net_core::protocols::keepalive;
use net_core::protocols::keepalive::KeepAlive;
use net_core::protocols::Role;
use net_core::protocols::Runner;
use net_core::types::Point;

use crate::connect;

/// KeepAlive ping interval.
const KEEPALIVE_INTERVAL: Duration = Duration::from_secs(20);

/// Rolling window of known chain points for intersection on reconnect.
struct ChainState {
    points: VecDeque<Point>,
    max_points: usize,
    block_no: u64,
}

impl ChainState {
    fn new(max_points: usize) -> Self {
        Self {
            points: VecDeque::new(),
            max_points,
            block_no: 0,
        }
    }

    fn roll_forward(&mut self, point: Point, block_no: u64) {
        self.block_no = block_no;
        if point == Point::Origin {
            return;
        }
        self.points.push_back(point);
        while self.points.len() > self.max_points {
            self.points.pop_front();
        }
    }

    fn roll_backward(&mut self, to: &Point) -> usize {
        let mut depth = 0;
        while let Some(back) = self.points.back() {
            if back == to {
                break;
            }
            self.points.pop_back();
            depth += 1;
        }
        depth
    }

    /// Build intersection candidates: geometric backoff from most recent,
    /// plus Origin as a fallback.
    fn intersection_points(&self) -> Vec<Point> {
        let len = self.points.len();
        let mut candidates = Vec::new();
        let mut offset = 0usize;

        while offset < len {
            candidates.push(self.points[len - 1 - offset].clone());
            if offset == 0 {
                offset = 1;
            } else {
                offset *= 2;
            }
        }

        candidates.push(Point::Origin);
        candidates
    }

    fn is_empty(&self) -> bool {
        self.points.is_empty()
    }
}

/// Spawn a background task that sends KeepAlive pings every KEEPALIVE_INTERVAL.
fn spawn_keepalive(
    ka_send: net_core::mux::CodecSend,
    ka_recv: net_core::mux::CodecRecv,
) -> tokio::task::JoinHandle<()> {
    tokio::spawn(async move {
        let mut runner = Runner::<KeepAlive>::new(Role::Client, ka_send, ka_recv);
        let mut cookie: u16 = 0;

        loop {
            tokio::time::sleep(KEEPALIVE_INTERVAL).await;
            cookie = cookie.wrapping_add(1);
            match keepalive::keep_alive(&mut runner, cookie).await {
                Ok(_rtt) => {}
                Err(_) => break, // connection lost, let the main loop handle reconnect
            }
        }
    })
}

pub async fn run(
    host: &str,
    magic: u64,
    max_rollback: usize,
) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
    let cs_proto = ProtocolConfig {
        id: chainsync::PROTOCOL_ID,
        priority: 1,
        ingress_limit: chainsync::INGRESS_LIMIT,
        egress_queue_size: 16,
    };
    let ka_proto = ProtocolConfig {
        id: keepalive::PROTOCOL_ID,
        priority: 7,
        ingress_limit: keepalive::INGRESS_LIMIT,
        egress_queue_size: 4,
    };

    let mut state = ChainState::new(max_rollback);
    let mut backoff = Duration::from_secs(1);
    let max_backoff = Duration::from_secs(30);

    loop {
        println!("connecting to {host}...");

        // Use a long SDU timeout — at tip we may wait minutes between blocks,
        // but KeepAlive pings keep the connection alive.
        let mux_config = MuxConfig {
            sdu_timeout: Duration::from_secs(900),
            ..MuxConfig::default()
        };

        let conn = match connect::connect_and_handshake_with_config(
            host,
            magic,
            &[cs_proto.clone(), ka_proto.clone()],
            mux_config,
        )
        .await
        {
            Ok(conn) => {
                backoff = Duration::from_secs(1);
                conn
            }
            Err(e) => {
                println!("connection failed: {e}");
                println!("  reconnecting in {backoff:?}...");
                tokio::time::sleep(backoff).await;
                backoff = (backoff * 2).min(max_backoff);
                continue;
            }
        };

        let mut channels = conn.channels.into_iter();
        let (cs_send, cs_recv) = channels.next().expect("chainsync channel");
        let (ka_send, ka_recv) = channels.next().expect("keepalive channel");

        // Start KeepAlive background pings.
        let ka_handle = spawn_keepalive(ka_send, ka_recv);

        let mut runner = Runner::<ChainSync>::new(Role::Client, cs_send, cs_recv);

        // Find intersection. On first connect (no known points), jump straight
        // to the current tip rather than syncing from genesis.
        let result = if state.is_empty() {
            match chainsync::find_intersection(&mut runner, vec![Point::Origin]).await {
                Ok(Some((_point, tip))) if tip.point != Point::Origin => {
                    println!("  tip is {tip}, jumping to it...");
                    chainsync::find_intersection(&mut runner, vec![tip.point]).await
                }
                other => other,
            }
        } else {
            let candidates = state.intersection_points();
            println!(
                "  finding intersection ({} candidates)...",
                candidates.len()
            );
            chainsync::find_intersection(&mut runner, candidates).await
        };

        match result {
            Ok(Some((point, tip))) => {
                println!("  intersection: {point}  tip: {tip}");
                state.roll_forward(tip.point.clone(), tip.block_no);
            }
            Ok(None) => {
                println!("  no intersection found, starting from origin");
            }
            Err(e) => {
                println!("  intersection error: {e}");
                ka_handle.abort();
                conn.running.abort();
                println!("  reconnecting in {backoff:?}...");
                tokio::time::sleep(backoff).await;
                backoff = (backoff * 2).min(max_backoff);
                continue;
            }
        }

        // Drain the initial rollback + re-delivery of the intersection point.
        let intersection_point = state.points.back().cloned();
        let mut drained = false;

        println!("  waiting for new blocks...");
        let mut last_block_time = Instant::now();

        let err = loop {
            match chainsync::request_next(&mut runner).await {
                Ok(ChainSyncEvent::RollForward { header: _, tip }) => {
                    if !drained {
                        if intersection_point.as_ref() == Some(&tip.point) {
                            drained = true;
                            last_block_time = Instant::now();
                            continue;
                        }
                        drained = true;
                    }

                    let elapsed = last_block_time.elapsed();
                    last_block_time = Instant::now();

                    state.roll_forward(tip.point.clone(), tip.block_no);

                    println!(
                        "  block #{:<8} {}  +{:.1}s",
                        tip.block_no,
                        tip.point,
                        elapsed.as_secs_f64(),
                    );
                }
                Ok(ChainSyncEvent::RollBackward { point, tip }) => {
                    let depth = state.roll_backward(&point);
                    state.block_no = tip.block_no;

                    if depth > 0 {
                        println!("  rollback to {}  depth={depth}  tip: {tip}", point);
                    }
                }
                Err(e) => break e,
            }
        };

        ka_handle.abort();
        conn.running.abort();
        println!("  connection lost: {err}");
        println!("  reconnecting in {backoff:?}...");
        tokio::time::sleep(backoff).await;
        backoff = (backoff * 2).min(max_backoff);
    }
}
