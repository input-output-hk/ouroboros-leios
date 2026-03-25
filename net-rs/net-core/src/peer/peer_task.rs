//! Per-peer task: manages one connection's protocol sub-tasks.
//!
//! Each peer task owns a single mux connection and spawns protocol-specific
//! sub-tasks. It translates raw protocol messages into `PeerEvent`s (sent
//! to the coordinator via a shared fan-in channel) and receives
//! `PeerCommand`s from the coordinator.

use std::time::Duration;

use tokio::sync::mpsc;
use tokio::task::JoinHandle;

use crate::mux::scheduler::priorities;
use crate::mux::{CodecRecv, CodecSend, MuxConfig, ProtocolConfig};
use crate::protocols::blockfetch::{self, BlockFetch};
use crate::protocols::chainsync::{self, ChainSync, ChainSyncEvent};
use crate::protocols::keepalive::{self, KeepAlive};
use crate::protocols::leios_fetch::{self, LeiosFetch};
use crate::protocols::leios_notify::{self, LeiosNotify, LeiosNotifyEvent};
use crate::protocols::peersharing::{self, PeerSharing};
use crate::protocols::{Role, Runner};
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
    pub leios_enabled: bool,
}

/// Protocol configs for client-side protocols (excluding handshake).
/// When `leios_enabled`, also registers LeiosNotify and LeiosFetch.
pub(crate) fn client_protocol_configs(leios_enabled: bool) -> Vec<ProtocolConfig> {
    let mut configs = vec![
        ProtocolConfig {
            id: chainsync::PROTOCOL_ID,
            priority: priorities::CHAINSYNC,
            ingress_limit: chainsync::INGRESS_LIMIT,
            egress_queue_size: 16,
        },
        ProtocolConfig {
            id: keepalive::PROTOCOL_ID,
            priority: priorities::KEEPALIVE,
            ingress_limit: keepalive::INGRESS_LIMIT,
            egress_queue_size: 4,
        },
        ProtocolConfig {
            id: blockfetch::PROTOCOL_ID,
            priority: priorities::BLOCKFETCH,
            ingress_limit: blockfetch::INGRESS_LIMIT,
            egress_queue_size: 16,
        },
        ProtocolConfig {
            id: peersharing::PROTOCOL_ID,
            priority: priorities::PEERSHARING,
            ingress_limit: peersharing::INGRESS_LIMIT,
            egress_queue_size: 4,
        },
    ];
    if leios_enabled {
        configs.push(ProtocolConfig {
            id: leios_notify::PROTOCOL_ID,
            priority: priorities::LEIOS_NOTIFY,
            ingress_limit: leios_notify::INGRESS_LIMIT,
            egress_queue_size: 16,
        });
        configs.push(ProtocolConfig {
            id: leios_fetch::PROTOCOL_ID,
            priority: priorities::LEIOS_FETCH,
            ingress_limit: leios_fetch::INGRESS_LIMIT,
            egress_queue_size: 16,
        });
    }
    configs
}

/// Spawn the ChainSync sub-task. Runs find_intersection then request_next loop.
pub(crate) fn spawn_chainsync(
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
                            header: crate::types::WrappedHeader::opaque(Vec::new()),
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
pub(crate) fn spawn_keepalive(
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
pub(crate) fn spawn_blockfetch(
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
pub(crate) fn spawn_peersharing(
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

/// Command sent to the LeiosFetch sub-task via an internal channel.
#[derive(Debug)]
pub(crate) enum LeiosFetchCommand {
    Block {
        point: Point,
    },
    BlockTxs {
        point: Point,
        bitmap: std::collections::BTreeMap<u16, u64>,
    },
    Votes {
        votes: Vec<(u64, Vec<u8>)>,
    },
}

/// Spawn the LeiosNotify sub-task. Continuous request_next loop.
pub(crate) fn spawn_leios_notify(
    ln_send: CodecSend,
    ln_recv: CodecRecv,
    peer_id: PeerId,
    event_sender: mpsc::Sender<(PeerId, PeerEvent)>,
) -> JoinHandle<()> {
    tokio::spawn(async move {
        let mut runner = Runner::<LeiosNotify>::new(Role::Client, ln_send, ln_recv);
        loop {
            match leios_notify::request_next(&mut runner).await {
                Ok(LeiosNotifyEvent::BlockAnnouncement { header }) => {
                    let _ = event_sender
                        .send((peer_id, PeerEvent::LeiosBlockAnnounced { header }))
                        .await;
                }
                Ok(LeiosNotifyEvent::BlockOffer { point }) => {
                    let _ = event_sender
                        .send((peer_id, PeerEvent::LeiosBlockOffered { point }))
                        .await;
                }
                Ok(LeiosNotifyEvent::BlockTxsOffer { point }) => {
                    let _ = event_sender
                        .send((peer_id, PeerEvent::LeiosBlockTxsOffered { point }))
                        .await;
                }
                Ok(LeiosNotifyEvent::VotesOffer { votes }) => {
                    let _ = event_sender
                        .send((peer_id, PeerEvent::LeiosVotesOffered { votes }))
                        .await;
                }
                Err(e) => {
                    let _ = event_sender
                        .send((
                            peer_id,
                            PeerEvent::Failed {
                                reason: format!("leios_notify: {e}"),
                            },
                        ))
                        .await;
                    return;
                }
            }
        }
    })
}

/// Spawn the LeiosFetch sub-task. Waits for fetch commands on the internal channel.
pub(crate) fn spawn_leios_fetch(
    lf_send: CodecSend,
    lf_recv: CodecRecv,
    peer_id: PeerId,
    mut command_receiver: mpsc::Receiver<LeiosFetchCommand>,
    event_sender: mpsc::Sender<(PeerId, PeerEvent)>,
) -> JoinHandle<()> {
    tokio::spawn(async move {
        let mut runner = Runner::<LeiosFetch>::new(Role::Client, lf_send, lf_recv);

        while let Some(cmd) = command_receiver.recv().await {
            match cmd {
                LeiosFetchCommand::Block { point } => {
                    match leios_fetch::fetch_block(&mut runner, point.clone()).await {
                        Ok(block) => {
                            let _ = event_sender
                                .send((peer_id, PeerEvent::LeiosBlockFetched { point, block }))
                                .await;
                        }
                        Err(e) => {
                            let _ = event_sender
                                .send((
                                    peer_id,
                                    PeerEvent::Failed {
                                        reason: format!("leios_fetch block: {e}"),
                                    },
                                ))
                                .await;
                            return;
                        }
                    }
                }
                LeiosFetchCommand::BlockTxs { point, bitmap } => {
                    match leios_fetch::fetch_block_txs(&mut runner, point.clone(), bitmap).await {
                        Ok(transactions) => {
                            let _ = event_sender
                                .send((
                                    peer_id,
                                    PeerEvent::LeiosBlockTxsFetched {
                                        point,
                                        transactions,
                                    },
                                ))
                                .await;
                        }
                        Err(e) => {
                            let _ = event_sender
                                .send((
                                    peer_id,
                                    PeerEvent::Failed {
                                        reason: format!("leios_fetch block_txs: {e}"),
                                    },
                                ))
                                .await;
                            return;
                        }
                    }
                }
                LeiosFetchCommand::Votes { votes } => {
                    match leios_fetch::fetch_votes(&mut runner, votes).await {
                        Ok(vote_data) => {
                            let _ = event_sender
                                .send((peer_id, PeerEvent::LeiosVotesFetched { votes: vote_data }))
                                .await;
                        }
                        Err(e) => {
                            let _ = event_sender
                                .send((
                                    peer_id,
                                    PeerEvent::Failed {
                                        reason: format!("leios_fetch votes: {e}"),
                                    },
                                ))
                                .await;
                            return;
                        }
                    }
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
        &client_protocol_configs(config.leios_enabled),
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

    // Conditionally spawn Leios sub-tasks.
    let leios_handles = if config.leios_enabled {
        let (ln_send, ln_recv) = channels
            .next()
            .expect("leios_notify channel registered fifth");
        let (lf_send, lf_recv) = channels
            .next()
            .expect("leios_fetch channel registered sixth");
        let (lf_cmd_sender, lf_cmd_receiver) = mpsc::channel::<LeiosFetchCommand>(16);
        let ln_handle = spawn_leios_notify(ln_send, ln_recv, peer_id, event_sender.clone());
        let lf_handle = spawn_leios_fetch(
            lf_send,
            lf_recv,
            peer_id,
            lf_cmd_receiver,
            event_sender.clone(),
        );
        Some((ln_handle, lf_handle, lf_cmd_sender))
    } else {
        None
    };

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
                    Some(PeerCommand::FetchLeiosBlock { point }) => {
                        if let Some((_, _, ref lf_sender)) = leios_handles {
                            let _ = lf_sender.send(LeiosFetchCommand::Block { point }).await;
                        }
                    }
                    Some(PeerCommand::FetchLeiosBlockTxs { point, bitmap }) => {
                        if let Some((_, _, ref lf_sender)) = leios_handles {
                            let _ = lf_sender.send(LeiosFetchCommand::BlockTxs { point, bitmap }).await;
                        }
                    }
                    Some(PeerCommand::FetchLeiosVotes { votes }) => {
                        if let Some((_, _, ref lf_sender)) = leios_handles {
                            let _ = lf_sender.send(LeiosFetchCommand::Votes { votes }).await;
                        }
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
    if let Some((ln_handle, lf_handle, _)) = leios_handles {
        ln_handle.abort();
        lf_handle.abort();
    }
    conn.running.abort();
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bearer::mem::MemBearer;
    use crate::mux::scheduler::RoundRobin;
    use crate::mux::{CodecRecv, CodecSend, MuxConfig, ProtocolConfig};
    use crate::mux::{Mux, MODE_INITIATOR, MODE_RESPONDER};
    use crate::protocols::chainsync::{ChainSync, Message as CsMsg};
    use crate::protocols::keepalive::{KeepAlive, Message as KaMsg};
    use crate::protocols::leios_fetch::{self, LeiosFetch, Message as LfMsg};
    use crate::protocols::leios_notify::{self, LeiosNotify, Message as LnMsg};
    use crate::protocols::Runner as ProtocolRunner;
    use crate::types::{BlockBody, Point, Tip, WrappedHeader};

    /// Minimal fake server: serves ChainSync and KeepAlive over MemBearer.
    /// Generates `block_count` blocks then holds at tip.
    async fn run_fake_server(bearer_b: MemBearer, magic: u64, block_count: usize) {
        use crate::mux::{CodecRecv, CodecSend, MuxConfig, ProtocolConfig};
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
                            header: WrappedHeader::opaque(vec![0xA0]), // minimal valid CBOR: empty map
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
        let protos = client_protocol_configs(false);

        let mut mux = Mux::new(MuxConfig::default(), RoundRobin::default(), MODE_INITIATOR);
        let (hs_send, hs_recv) = mux.register(&hs_proto);
        let mut channels = Vec::new();
        for proto in &protos {
            let (send, recv) = mux.register(proto);
            channels.push((
                crate::mux::CodecSend::new(send),
                crate::mux::CodecRecv::new(recv),
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
            crate::mux::CodecSend::new(hs_send),
            crate::mux::CodecRecv::new(hs_recv),
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
    async fn spawn_leios_notify_receives_offers() {
        let ln_proto = ProtocolConfig {
            id: leios_notify::PROTOCOL_ID,
            priority: 0,
            ingress_limit: leios_notify::INGRESS_LIMIT,
            egress_queue_size: 16,
        };

        let ((client_send, client_recv), (server_send, server_recv), mux_a, mux_b) =
            mux_pair_for_protocol(&ln_proto);

        // Fake server: respond to two request_next calls, then expect MsgDone.
        let server_handle = tokio::spawn(async move {
            let mut runner =
                ProtocolRunner::<LeiosNotify>::new(Role::Server, server_send, server_recv);

            // First: receive request, reply with block offer.
            let msg = runner.recv().await.unwrap();
            assert!(matches!(msg, LnMsg::MsgLeiosNotificationRequestNext));
            runner
                .send(&LnMsg::MsgLeiosBlockOffer {
                    point: Point::Specific {
                        slot: 42,
                        hash: [0xAB; 32],
                    },
                })
                .await
                .unwrap();

            // Second: receive request, reply with votes offer.
            let msg = runner.recv().await.unwrap();
            assert!(matches!(msg, LnMsg::MsgLeiosNotificationRequestNext));
            runner
                .send(&LnMsg::MsgLeiosVotesOffer {
                    votes: vec![(100, vec![0x01])],
                })
                .await
                .unwrap();

            // Client will be aborted, so the next recv will fail — that's fine.
            let _ = runner.recv().await;
        });

        let (event_sender, mut event_receiver) = mpsc::channel(64);
        let peer_id = PeerId(1);

        let ln_handle = spawn_leios_notify(client_send, client_recv, peer_id, event_sender);

        // Collect two events with timeout.
        let result = tokio::time::timeout(Duration::from_secs(5), async {
            let (_id, event1) = event_receiver.recv().await.unwrap();
            match event1 {
                PeerEvent::LeiosBlockOffered { point } => {
                    assert_eq!(
                        point,
                        Point::Specific {
                            slot: 42,
                            hash: [0xAB; 32]
                        }
                    );
                }
                other => panic!("expected LeiosBlockOffered, got {other:?}"),
            }

            let (_id, event2) = event_receiver.recv().await.unwrap();
            match event2 {
                PeerEvent::LeiosVotesOffered { votes } => {
                    assert_eq!(votes, vec![(100, vec![0x01])]);
                }
                other => panic!("expected LeiosVotesOffered, got {other:?}"),
            }
        })
        .await;

        assert!(result.is_ok(), "timed out waiting for Leios notify events");

        // Clean up.
        ln_handle.abort();
        server_handle.abort();
        mux_a.abort();
        mux_b.abort();
    }

    #[tokio::test]
    async fn spawn_leios_fetch_fetches_block() {
        let lf_proto = ProtocolConfig {
            id: leios_fetch::PROTOCOL_ID,
            priority: 0,
            ingress_limit: leios_fetch::INGRESS_LIMIT,
            egress_queue_size: 16,
        };

        let ((client_send, client_recv), (server_send, server_recv), mux_a, mux_b) =
            mux_pair_for_protocol(&lf_proto);

        // Fake server: receive block request, reply with block, then expect MsgDone.
        let server_handle = tokio::spawn(async move {
            let mut runner =
                ProtocolRunner::<LeiosFetch>::new(Role::Server, server_send, server_recv);

            let msg = runner.recv().await.unwrap();
            match msg {
                LfMsg::MsgLeiosBlockRequest { point } => {
                    assert_eq!(point, Point::Specific { slot: 42, hash: [0xAB; 32] });
                }
                other => panic!("expected MsgLeiosBlockRequest, got {other:?}"),
            }
            runner
                .send(&LfMsg::MsgLeiosBlock {
                    block: vec![1, 2, 3, 4],
                })
                .await
                .unwrap();

            // Expect MsgDone (client channel closes after command_sender is dropped).
            let _ = runner.recv().await;
        });

        let (event_sender, mut event_receiver) = mpsc::channel(64);
        let (command_sender, command_receiver) = mpsc::channel::<LeiosFetchCommand>(16);
        let peer_id = PeerId(1);

        let lf_handle = spawn_leios_fetch(
            client_send,
            client_recv,
            peer_id,
            command_receiver,
            event_sender,
        );

        // Send a fetch command.
        command_sender
            .send(LeiosFetchCommand::Block {
                point: Point::Specific {
                    slot: 42,
                    hash: [0xAB; 32],
                },
            })
            .await
            .unwrap();

        // Collect the event.
        let result = tokio::time::timeout(Duration::from_secs(5), async {
            let (_id, event) = event_receiver.recv().await.unwrap();
            match event {
                PeerEvent::LeiosBlockFetched { point, block } => {
                    assert_eq!(
                        point,
                        Point::Specific {
                            slot: 42,
                            hash: [0xAB; 32]
                        }
                    );
                    assert_eq!(block, vec![1, 2, 3, 4]);
                }
                other => panic!("expected LeiosBlockFetched, got {other:?}"),
            }
        })
        .await;

        assert!(result.is_ok(), "timed out waiting for LeiosBlockFetched");

        // Clean up.
        drop(command_sender);
        lf_handle.abort();
        server_handle.abort();
        mux_a.abort();
        mux_b.abort();
    }
}
