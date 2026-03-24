//! Per-peer task: manages one connection's protocol sub-tasks.
//!
//! Each peer task owns a single mux connection and spawns protocol-specific
//! sub-tasks. It translates raw protocol messages into `PeerEvent`s (sent
//! to the coordinator via a shared fan-in channel) and receives
//! `PeerCommand`s from the coordinator.

use std::time::Duration;

use tokio::sync::mpsc;
use tokio::task::JoinHandle;

use crate::codec::{CodecRecv, CodecSend};
use crate::mux::{MuxConfig, ProtocolConfig};
use crate::protocol::{Role, Runner};
use crate::protocols::blockfetch::{self, BlockFetch};
use crate::protocols::chainsync::{self, ChainSync, ChainSyncEvent};
use crate::protocols::keepalive::{self, KeepAlive};
use crate::protocols::peersharing::{self, PeerSharing};
use crate::types::Point;

use super::connect::{self, Connection};
use super::types::{PeerCommand, PeerEvent};
use super::PeerId;

/// Configuration for a peer task.
pub(crate) struct PeerTaskConfig {
    pub peer_id: PeerId,
    pub address: String,
    pub network_magic: u64,
    pub keepalive_interval: Duration,
    pub sdu_timeout: Duration,
    pub event_sender: mpsc::Sender<(PeerId, PeerEvent)>,
    pub command_receiver: mpsc::Receiver<PeerCommand>,
}

/// Protocol configs for the 5 client-side protocols (excluding handshake).
fn client_protocol_configs() -> Vec<ProtocolConfig> {
    vec![
        ProtocolConfig {
            id: chainsync::PROTOCOL_ID,
            priority: 1,
            ingress_limit: chainsync::INGRESS_LIMIT,
            egress_queue_size: 16,
        },
        ProtocolConfig {
            id: keepalive::PROTOCOL_ID,
            priority: 7,
            ingress_limit: keepalive::INGRESS_LIMIT,
            egress_queue_size: 4,
        },
        ProtocolConfig {
            id: blockfetch::PROTOCOL_ID,
            priority: 2,
            ingress_limit: blockfetch::INGRESS_LIMIT,
            egress_queue_size: 16,
        },
        ProtocolConfig {
            id: peersharing::PROTOCOL_ID,
            priority: 7,
            ingress_limit: peersharing::INGRESS_LIMIT,
            egress_queue_size: 4,
        },
    ]
}

/// Spawn the ChainSync sub-task. Runs find_intersection then request_next loop.
fn spawn_chainsync(
    cs_send: CodecSend,
    cs_recv: CodecRecv,
    peer_id: PeerId,
    event_sender: mpsc::Sender<(PeerId, PeerEvent)>,
) -> JoinHandle<()> {
    tokio::spawn(async move {
        let mut runner = Runner::<ChainSync>::new(Role::Client, cs_send, cs_recv);

        // Jump to current tip rather than syncing from genesis.
        let result = match chainsync::find_intersection(&mut runner, vec![Point::Origin]).await {
            Ok(Some((_point, tip))) if tip.point != Point::Origin => {
                chainsync::find_intersection(&mut runner, vec![tip.point]).await
            }
            other => other,
        };

        match result {
            Ok(Some((_point, tip))) => {
                let _ = event_sender
                    .send((
                        peer_id,
                        PeerEvent::HeaderAnnounced {
                            header: crate::types::WrappedHeader(Vec::new()),
                            tip,
                        },
                    ))
                    .await;
            }
            Ok(None) => { /* no intersection, continue from origin */ }
            Err(e) => {
                let _ = event_sender
                    .send((
                        peer_id,
                        PeerEvent::Failed {
                            reason: format!("chainsync intersection: {e}"),
                        },
                    ))
                    .await;
                return;
            }
        }

        // Main request_next loop.
        loop {
            match chainsync::request_next(&mut runner).await {
                Ok(ChainSyncEvent::RollForward { header, tip }) => {
                    let _ = event_sender
                        .send((peer_id, PeerEvent::HeaderAnnounced { header, tip }))
                        .await;
                }
                Ok(ChainSyncEvent::RollBackward { point, tip }) => {
                    let _ = event_sender
                        .send((peer_id, PeerEvent::RolledBack { point, tip }))
                        .await;
                }
                Err(e) => {
                    let _ = event_sender
                        .send((
                            peer_id,
                            PeerEvent::Failed {
                                reason: format!("chainsync: {e}"),
                            },
                        ))
                        .await;
                    return;
                }
            }
        }
    })
}

/// Spawn the KeepAlive sub-task. Periodic pings on an interval.
fn spawn_keepalive(
    ka_send: CodecSend,
    ka_recv: CodecRecv,
    peer_id: PeerId,
    interval: Duration,
    event_sender: mpsc::Sender<(PeerId, PeerEvent)>,
) -> JoinHandle<()> {
    tokio::spawn(async move {
        let mut runner = Runner::<KeepAlive>::new(Role::Client, ka_send, ka_recv);
        let mut cookie: u16 = 0;

        loop {
            tokio::time::sleep(interval).await;
            cookie = cookie.wrapping_add(1);
            match keepalive::keep_alive(&mut runner, cookie).await {
                Ok(rtt) => {
                    let _ = event_sender
                        .send((peer_id, PeerEvent::LatencyMeasured { rtt }))
                        .await;
                }
                Err(e) => {
                    let _ = event_sender
                        .send((
                            peer_id,
                            PeerEvent::Failed {
                                reason: format!("keepalive: {e}"),
                            },
                        ))
                        .await;
                    return;
                }
            }
        }
    })
}

/// Spawn the BlockFetch sub-task. Waits for fetch commands on the internal channel.
fn spawn_blockfetch(
    bf_send: CodecSend,
    bf_recv: CodecRecv,
    peer_id: PeerId,
    mut fetch_receiver: mpsc::Receiver<(Point, Point)>,
    event_sender: mpsc::Sender<(PeerId, PeerEvent)>,
) -> JoinHandle<()> {
    tokio::spawn(async move {
        let mut runner = Runner::<BlockFetch>::new(Role::Client, bf_send, bf_recv);

        while let Some((from, to)) = fetch_receiver.recv().await {
            match blockfetch::request_range(&mut runner, from.clone(), to.clone()).await {
                Ok(true) => {
                    // Stream blocks until batch done.
                    loop {
                        match blockfetch::recv_block(&mut runner).await {
                            Ok(Some(body)) => {
                                // We don't know the exact point for each block in
                                // the stream — use `to` for the last one. For now
                                // send each block as it arrives with the range end.
                                let _ = event_sender
                                    .send((
                                        peer_id,
                                        PeerEvent::BlockFetched {
                                            point: to.clone(),
                                            body,
                                        },
                                    ))
                                    .await;
                            }
                            Ok(None) => break, // batch complete
                            Err(e) => {
                                let _ = event_sender
                                    .send((
                                        peer_id,
                                        PeerEvent::Failed {
                                            reason: format!("blockfetch stream: {e}"),
                                        },
                                    ))
                                    .await;
                                return;
                            }
                        }
                    }
                }
                Ok(false) => {
                    // NoBlocks — peer doesn't have this range.
                    tracing::warn!("peer {peer_id}: no blocks for range {from}..{to}");
                }
                Err(e) => {
                    let _ = event_sender
                        .send((
                            peer_id,
                            PeerEvent::Failed {
                                reason: format!("blockfetch request: {e}"),
                            },
                        ))
                        .await;
                    return;
                }
            }
        }
    })
}

/// Spawn the PeerSharing sub-task. Waits for share requests on the internal channel.
fn spawn_peersharing(
    ps_send: CodecSend,
    ps_recv: CodecRecv,
    peer_id: PeerId,
    mut request_receiver: mpsc::Receiver<u8>,
    event_sender: mpsc::Sender<(PeerId, PeerEvent)>,
) -> JoinHandle<()> {
    tokio::spawn(async move {
        let mut runner = Runner::<PeerSharing>::new(Role::Client, ps_send, ps_recv);

        while let Some(amount) = request_receiver.recv().await {
            match peersharing::share_request(&mut runner, amount).await {
                Ok(peers) => {
                    let _ = event_sender
                        .send((peer_id, PeerEvent::PeersDiscovered { peers }))
                        .await;
                }
                Err(e) => {
                    let _ = event_sender
                        .send((
                            peer_id,
                            PeerEvent::Failed {
                                reason: format!("peersharing: {e}"),
                            },
                        ))
                        .await;
                    return;
                }
            }
        }
    })
}

/// Run the per-peer task. Connects, spawns protocol sub-tasks, and
/// dispatches commands from the coordinator.
pub(crate) async fn run_peer_task(mut config: PeerTaskConfig) {
    let peer_id = config.peer_id;
    let event_sender = config.event_sender.clone();

    // Connect and handshake.
    let mux_config = MuxConfig {
        sdu_timeout: config.sdu_timeout,
        ..MuxConfig::default()
    };

    let conn: Connection = match connect::connect_and_handshake_with_config(
        &config.address,
        config.network_magic,
        &client_protocol_configs(),
        mux_config,
    )
    .await
    {
        Ok(conn) => conn,
        Err(e) => {
            let reason = format!("connect: {e}");
            let _ = event_sender
                .send((peer_id, PeerEvent::Failed { reason }))
                .await;
            return;
        }
    };

    // Report successful connection.
    let _ = event_sender.send((peer_id, PeerEvent::Connected)).await;

    // Extract codec pairs (in registration order).
    let mut channels = conn.channels.into_iter();
    let (cs_send, cs_recv) = channels.next().expect("chainsync channel registered first");
    let (ka_send, ka_recv) = channels
        .next()
        .expect("keepalive channel registered second");
    let (bf_send, bf_recv) = channels
        .next()
        .expect("blockfetch channel registered third");
    let (ps_send, ps_recv) = channels
        .next()
        .expect("peersharing channel registered fourth");

    // Internal channels for dispatching commands to sub-tasks.
    let (fetch_sender, fetch_receiver) = mpsc::channel::<(Point, Point)>(16);
    let (peer_share_sender, peer_share_receiver) = mpsc::channel::<u8>(4);

    // Spawn protocol sub-tasks.
    let mut cs_handle = spawn_chainsync(cs_send, cs_recv, peer_id, event_sender.clone());
    let ka_handle = spawn_keepalive(
        ka_send,
        ka_recv,
        peer_id,
        config.keepalive_interval,
        event_sender.clone(),
    );
    let bf_handle = spawn_blockfetch(
        bf_send,
        bf_recv,
        peer_id,
        fetch_receiver,
        event_sender.clone(),
    );
    let ps_handle = spawn_peersharing(
        ps_send,
        ps_recv,
        peer_id,
        peer_share_receiver,
        event_sender.clone(),
    );

    // Main select loop: dispatch commands and detect sub-task failure.
    // ChainSync is the primary protocol — if it exits, the peer is done.
    loop {
        tokio::select! {
            cmd = config.command_receiver.recv() => {
                match cmd {
                    Some(PeerCommand::FetchBlocks { from, to }) => {
                        let _ = fetch_sender.send((from, to)).await;
                    }
                    Some(PeerCommand::RequestPeers { amount }) => {
                        let _ = peer_share_sender.send(amount).await;
                    }
                    Some(PeerCommand::Disconnect) | None => {
                        break;
                    }
                }
            }
            // If ChainSync exits, the peer is done.
            result = &mut cs_handle => {
                if let Err(e) = result {
                    tracing::warn!("peer {peer_id}: chainsync task panicked: {e}");
                }
                break;
            }
        }
    }

    // Clean up: abort all sub-tasks and the mux.
    cs_handle.abort();
    ka_handle.abort();
    bf_handle.abort();
    ps_handle.abort();
    conn.running.abort();
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bearer::mem::MemBearer;
    use crate::mux::scheduler::RoundRobin;
    use crate::mux::{Mux, MODE_INITIATOR, MODE_RESPONDER};
    use crate::protocol::Runner as ProtocolRunner;
    use crate::protocols::chainsync::{ChainSync, Message as CsMsg};
    use crate::protocols::keepalive::{KeepAlive, Message as KaMsg};
    use crate::types::{BlockBody, Point, Tip, WrappedHeader};

    /// Minimal fake server: serves ChainSync and KeepAlive over MemBearer.
    /// Generates `block_count` blocks then holds at tip.
    async fn run_fake_server(bearer_b: MemBearer, magic: u64, block_count: usize) {
        use crate::codec::{CodecRecv, CodecSend};
        use crate::mux::{MuxConfig, ProtocolConfig};
        use crate::protocols::handshake;

        let hs_proto = ProtocolConfig {
            id: handshake::PROTOCOL_ID,
            priority: 0,
            ingress_limit: handshake::SIZE_LIMIT,
            egress_queue_size: 4,
        };
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
        let bf_proto = ProtocolConfig {
            id: blockfetch::PROTOCOL_ID,
            priority: 2,
            ingress_limit: blockfetch::INGRESS_LIMIT,
            egress_queue_size: 16,
        };
        let ps_proto = ProtocolConfig {
            id: peersharing::PROTOCOL_ID,
            priority: 7,
            ingress_limit: peersharing::INGRESS_LIMIT,
            egress_queue_size: 4,
        };

        let mut mux = Mux::new(MuxConfig::default(), RoundRobin::default(), MODE_RESPONDER);
        let (hs_send, hs_recv) = mux.register(&hs_proto);
        let (cs_send, cs_recv) = mux.register(&cs_proto);
        let (ka_send, ka_recv) = mux.register(&ka_proto);
        let (_bf_send, _bf_recv) = mux.register(&bf_proto);
        let (_ps_send, _ps_recv) = mux.register(&ps_proto);

        let running = mux.run(bearer_b);

        // Server-side handshake.
        let hs_result = handshake::run_server(
            CodecSend::new(hs_send),
            CodecRecv::new(hs_recv),
            |client_versions| crate::protocols::handshake::n2n::negotiate(client_versions, magic),
        )
        .await;

        if hs_result.is_err() {
            running.abort();
            return;
        }

        // Spawn KeepAlive responder.
        let ka_handle = tokio::spawn(async move {
            let mut runner = ProtocolRunner::<KeepAlive>::new(
                Role::Server,
                CodecSend::new(ka_send),
                CodecRecv::new(ka_recv),
            );
            loop {
                match runner.recv().await {
                    Ok(KaMsg::MsgKeepAlive { cookie }) => {
                        if runner
                            .send(&KaMsg::MsgKeepAliveResponse { cookie })
                            .await
                            .is_err()
                        {
                            break;
                        }
                    }
                    _ => break,
                }
            }
        });

        // Serve ChainSync: generate blocks then await at tip.
        let mut runner = ProtocolRunner::<ChainSync>::new(
            Role::Server,
            CodecSend::new(cs_send),
            CodecRecv::new(cs_recv),
        );

        // Generate fake block points.
        let blocks: Vec<(Point, Tip)> = (1..=block_count)
            .map(|i| {
                let hash: [u8; 32] = [i as u8; 32];
                let point = Point::Specific {
                    slot: i as u64,
                    hash,
                };
                let tip = Tip {
                    point: point.clone(),
                    block_no: i as u64,
                };
                (point, tip)
            })
            .collect();

        let final_tip = blocks.last().map(|(_, tip)| tip.clone()).unwrap_or(Tip {
            point: Point::Origin,
            block_no: 0,
        });

        loop {
            let msg = match runner.recv().await {
                Ok(msg) => msg,
                Err(_) => break,
            };

            match msg {
                CsMsg::MsgFindIntersect { points } => {
                    if points.contains(&Point::Origin)
                        || points.iter().any(|p| blocks.iter().any(|(bp, _)| bp == p))
                    {
                        // Find the best intersection.
                        let best = points.iter().rev().find_map(|p| {
                            if p == &Point::Origin {
                                Some((Point::Origin, final_tip.clone()))
                            } else {
                                blocks
                                    .iter()
                                    .find(|(bp, _)| bp == p)
                                    .map(|(bp, _)| (bp.clone(), final_tip.clone()))
                            }
                        });
                        if let Some((point, tip)) = best {
                            let _ = runner.send(&CsMsg::MsgIntersectFound { point, tip }).await;
                        } else {
                            let _ = runner
                                .send(&CsMsg::MsgIntersectNotFound {
                                    tip: final_tip.clone(),
                                })
                                .await;
                        }
                    } else {
                        let _ = runner
                            .send(&CsMsg::MsgIntersectNotFound {
                                tip: final_tip.clone(),
                            })
                            .await;
                    }
                }
                CsMsg::MsgRequestNext => {
                    // For simplicity, always send the final tip as a roll forward,
                    // then await. A real server would track the client's position.
                    let _ = runner
                        .send(&CsMsg::MsgRollForward {
                            header: WrappedHeader(vec![0xA0]), // minimal valid CBOR: empty map
                            tip: final_tip.clone(),
                        })
                        .await;
                }
                CsMsg::MsgDone => break,
                _ => {}
            }
        }

        ka_handle.abort();
        running.abort();
    }

    #[tokio::test]
    async fn peer_task_receives_header_announced() {
        let magic = 764824073;
        let (bearer_a, bearer_b) = MemBearer::pair();

        // Start fake server.
        let server_handle = tokio::spawn(run_fake_server(bearer_b, magic, 3));

        // Set up peer task channels.
        let (event_sender, mut event_receiver) = mpsc::channel(64);
        let (command_sender, command_receiver) = mpsc::channel::<PeerCommand>(16);
        let peer_id = PeerId(1);

        // We can't use connect_and_handshake (it does TCP), so we need to
        // set up the mux manually for the client side over MemBearer.
        // Instead, test the sub-task spawning directly.

        // Set up client-side mux.
        let hs_proto = ProtocolConfig {
            id: crate::protocols::handshake::PROTOCOL_ID,
            priority: 0,
            ingress_limit: crate::protocols::handshake::SIZE_LIMIT,
            egress_queue_size: 4,
        };
        let protos = client_protocol_configs();

        let mut mux = Mux::new(MuxConfig::default(), RoundRobin::default(), MODE_INITIATOR);
        let (hs_send, hs_recv) = mux.register(&hs_proto);
        let mut channels = Vec::new();
        for proto in &protos {
            let (send, recv) = mux.register(proto);
            channels.push((
                crate::codec::CodecSend::new(send),
                crate::codec::CodecRecv::new(recv),
            ));
        }
        let running = mux.run(bearer_a);

        // Client-side handshake.
        use crate::protocols::handshake;
        use crate::protocols::handshake::n2n;
        let versions = n2n::version_table(&n2n::VersionData {
            network_magic: magic,
            initiator_only_diffusion_mode: false,
            peer_sharing: 0,
            query: false,
        });
        let hs_result = handshake::run_client(
            crate::codec::CodecSend::new(hs_send),
            crate::codec::CodecRecv::new(hs_recv),
            versions,
        )
        .await;
        assert!(hs_result.is_ok());

        let mut channels = channels.into_iter();
        let (cs_send, cs_recv) = channels.next().unwrap();
        let (ka_send, ka_recv) = channels.next().unwrap();
        let (_bf_send, _bf_recv) = channels.next().unwrap();
        let (_ps_send, _ps_recv) = channels.next().unwrap();

        // Spawn just ChainSync and KeepAlive sub-tasks.
        let cs_handle = spawn_chainsync(cs_send, cs_recv, peer_id, event_sender.clone());
        let ka_handle = spawn_keepalive(
            ka_send,
            ka_recv,
            peer_id,
            Duration::from_secs(60),
            event_sender.clone(),
        );

        // Collect events. We should get at least one HeaderAnnounced.
        let mut got_header = false;
        let timeout = tokio::time::timeout(Duration::from_secs(5), async {
            while let Some((_id, event)) = event_receiver.recv().await {
                match event {
                    PeerEvent::HeaderAnnounced { tip, .. } => {
                        assert!(tip.block_no > 0);
                        got_header = true;
                        break;
                    }
                    PeerEvent::Failed { reason } => {
                        panic!("unexpected failure: {reason}");
                    }
                    _ => {}
                }
            }
        })
        .await;

        assert!(timeout.is_ok(), "timed out waiting for HeaderAnnounced");
        assert!(got_header, "should have received HeaderAnnounced");

        // Clean up.
        cs_handle.abort();
        ka_handle.abort();
        running.abort();
        drop(command_sender);
        server_handle.abort();
    }
}
