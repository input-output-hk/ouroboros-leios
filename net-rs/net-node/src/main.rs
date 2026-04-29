mod chain_tree;
mod clock;
mod config;
mod consensus;
mod mempool;
mod network;
mod production;
mod telemetry;
mod validation;

use clap::Parser;
use net_core::multi_peer::types::{NetworkCommand, NetworkEvent};
use tokio::io::AsyncBufReadExt;
use tracing::{info, warn};

use telemetry::NodeEvent;

#[derive(Parser)]
#[command(name = "net-node", about = "Cardano Leios test node")]
struct Cli {
    /// TOML config files (repeatable, layered left-to-right).
    #[arg(long = "config", value_name = "FILE")]
    configs: Vec<String>,

    /// Override individual config values (repeatable, key=value).
    #[arg(long = "set", value_name = "KEY=VALUE")]
    set: Vec<String>,
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
    tracing_subscriber::fmt::init();

    let cli = Cli::parse();
    let config = config::load(&cli.configs, &cli.set)?;

    info!(
        node_id = %config.node_id,
        listen = ?config.listen_address,
        magic = config.network_magic,
        slot_ms = config.slot_duration_ms,
        leios = config.leios_enabled,
        peers = config.peers.len(),
        stake = config.production.stake,
        total_stake = config.production.total_stake,
        tx_rate = config.transactions.tx_rate,
        "starting node"
    );

    let mut slot_clock = clock::SlotClock::new(config.genesis_time_unix, config.slot_duration_ms);

    // Mempool: shared between tx generator, block producer, and the Leios
    // store's TxBodyResolver (so receiver-side EB tx requests can be served
    // from the mempool).
    let mempool = mempool::new_mempool(config.transactions.mempool_capacity);
    let tx_body_resolver: std::sync::Arc<dyn net_core::store::leios_store::TxBodyResolver> =
        std::sync::Arc::new(mempool::MempoolTxBodyResolver::new(mempool.clone()));

    let mut handle = network::start(&config, Some(tx_body_resolver)).await?;
    let commands = handle.commands.clone();

    // Dynamic config watch channel (hot-reloadable parameters).
    let (dyn_tx, dyn_rx) = tokio::sync::watch::channel(config.dynamic_config());

    // Block producer.
    let mut producer =
        production::BlockProducer::new(&config.production, config.seed, dyn_rx.clone());
    if producer.is_active() {
        info!(
            node_id = %config.node_id,
            stake = config.production.stake,
            total_stake = config.production.total_stake,
            rb_prob = config.production.rb_generation_probability,
            eb_prob = config.production.eb_generation_probability,
            vote_prob = config.production.vote_generation_probability,
            "block production enabled"
        );
    }

    // Validator and consensus. The persistent committee allocation must
    // be deterministic across the network; seed it from genesis_time so
    // every node arrives at the same wFA committee.
    let (validator, mut validation_rx) = validation::Validator::new(dyn_rx.clone());
    let stake_registry = if config.production.stake_registry.is_empty() {
        vec![config::StakeEntry {
            node_id: config.node_id.clone(),
            stake: config.production.stake,
        }]
    } else {
        config.production.stake_registry.clone()
    };
    let mut consensus = consensus::Consensus::new(
        config.node_id.clone(),
        commands.clone(),
        validator,
        mempool.clone(),
        config.security_param_k,
        consensus::PipelineConfig {
            delta_hdr: config.production.leios_delta_hdr_slots,
            vote_window: config.production.leios_vote_window_slots,
            diffuse_window: config.production.leios_diffuse_window_slots,
            dedup_window: config.leios_dedup_window,
        },
        config.production.committee_selection.clone(),
        config.production.stake,
        &stake_registry,
        config.production.persistent_vote_bytes,
        config.production.non_persistent_vote_bytes,
        config.production.quorum_stake_fraction,
        config.genesis_time_unix,
        config.seed,
        dyn_rx.clone(),
    );

    // Transaction validator (validates received txs before mempool entry).
    let (tx_valid_tx, tx_valid_rx) = tokio::sync::mpsc::channel::<Vec<u8>>(1024);
    let _tx_valid_handle = mempool::spawn_tx_validator(
        config.validation.tx_validation_ms,
        config.validation.tx_validation_ms_per_byte,
        mempool.clone(),
        tx_valid_rx,
    );

    // Transaction generator (background task).
    let _tx_handle = mempool::spawn_tx_generator(
        &config.transactions,
        config.seed,
        mempool.clone(),
        config.node_id.clone(),
        dyn_rx.clone(),
    );

    // Telemetry.
    let mut telem = telemetry::TelemetryHandle::new(
        &config.telemetry,
        config.node_id.clone(),
        config.genesis_time_unix,
    )?;

    // Stats timer.
    let stats_interval = if telem.has_stats_sinks() && config.telemetry.stats_interval_secs > 0 {
        config.telemetry.stats_interval_secs
    } else {
        0
    };
    let mut stats_tick = tokio::time::interval(if stats_interval > 0 {
        std::time::Duration::from_secs(stats_interval)
    } else {
        std::time::Duration::from_secs(86400) // effectively disabled
    });
    stats_tick.tick().await; // consume initial immediate tick

    // Graceful shutdown on Ctrl-C.
    let shutdown = tokio::signal::ctrl_c();
    tokio::pin!(shutdown);

    // Stdin reader for dynamic config updates from net-cluster.
    let stdin = tokio::io::stdin();
    let mut stdin_reader = tokio::io::BufReader::new(stdin);
    let mut stdin_line = String::new();

    let leios = config.leios_enabled;
    let node_id = config.node_id.clone();

    let mut retry_counter: u64 = 0;
    loop {
        tokio::select! {
            slot = slot_clock.tick() => {
                telem.current_slot = slot;
                retry_counter += 1;

                // Leios: advance pipeline phases and trigger voting.
                if leios {
                    consensus.on_slot(slot).await;
                    for ev in consensus.drain_leios_telemetry() {
                        telem.record(ev).await;
                    }
                }

                // Praos: try to produce a ranking block. If the mempool
                // overflows rb_body_max_bytes, an EB manifest is produced
                // instead of embedding txs in the RB body.
                let prev_hash = consensus.tip_hash();
                let next_block_no = consensus.next_block_number();
                let certified_eb = leios && consensus.has_certified_eb();
                let certified_eb_slot = if certified_eb { consensus.certified_eb_slot() } else { None };
                if let Some(produced) = producer.try_produce_block(slot, prev_hash, next_block_no, certified_eb, &mempool) {
                    info!(
                        node_id = %node_id,
                        point = %produced.point,
                        block_count = producer.block_count(),
                        tx_count = produced.included_tx_count,
                        has_eb = produced.announced_eb.is_some(),
                        "produced block"
                    );
                    telem.blocks_produced += 1;
                    telem.record(NodeEvent::RBGenerated {
                        node: node_id.clone(),
                        slot,
                        size_bytes: produced.body.raw.len(),
                    }).await;
                    if let Some(eb_slot) = certified_eb_slot {
                        telem.record(NodeEvent::RbCertifiedEb {
                            node: node_id.clone(),
                            rb_slot: slot,
                            eb_slot,
                        }).await;
                    }

                    // If an EB was produced (overflow path), inject it.
                    if let Some(ref eb) = produced.announced_eb {
                        info!(node_id = %node_id, %eb.point, "produced endorser block (overflow)");
                        telem.record(NodeEvent::EBGenerated {
                            node: node_id.clone(),
                            slot,
                        }).await;
                        let _ = commands.send(NetworkCommand::InjectLeiosBlock {
                            point: eb.point.clone(),
                            block: eb.data.clone(),
                        }).await;
                        let _ = commands.send(NetworkCommand::InjectLeiosBlockTxs {
                            point: eb.point.clone(),
                            transactions: eb.transactions.clone(),
                        }).await;
                    }

                    consensus
                        .register_self_produced(&produced.point, &produced.header, &produced.body)
                        .await;
                }

                // Periodic retry: re-run chain selection every 5 slots
                // to recover from stale fetches and pending_validation
                // deadlocks, even when no new network events arrive.
                if retry_counter.is_multiple_of(5) {
                    consensus.retry_pending().await;
                }
            }
            event = handle.events.recv() => {
                match event {
                    Some(event) => {
                        // Validate received txs before mempool entry.
                        if let NetworkEvent::TransactionReceived { body, .. } = &event {
                            let _ = tx_valid_tx.try_send(body.clone());
                        }
                        // Same path for Leios EB tx bodies fetched by bitmap.
                        // Hash-verify each body against the cached manifest;
                        // the wire format gives no per-body index, so the
                        // server's response order can't be trusted alone.
                        if let NetworkEvent::LeiosBlockTxsReceived { point, transactions } = &event {
                            let outcome = consensus.match_eb_tx_response(point, transactions);
                            if outcome.requested > 0 && outcome.matched_bodies.len() < outcome.requested {
                                tracing::warn!(
                                    node_id = %node_id,
                                    %point,
                                    requested = outcome.requested,
                                    matched = outcome.matched_bodies.len(),
                                    remaining_segments = outcome.remaining_bitmap.len(),
                                    "leios block txs response is partial — retrying"
                                );
                            }
                            for body in &outcome.matched_bodies {
                                let _ = tx_valid_tx.try_send(body.clone());
                            }
                            if !outcome.remaining_bitmap.is_empty() {
                                consensus
                                    .retry_eb_tx_fetch(point.clone(), outcome.remaining_bitmap)
                                    .await;
                            }
                        }
                        // Pull-model TxSubmission: provide txs from mempool on demand.
                        // peek_unannounced_for_peer returns only txs we have
                        // not already advertised to this peer, preventing the
                        // hot-loop where every cycle re-clones and re-ships
                        // the same head-of-mempool txs.
                        if let NetworkEvent::TxsRequested { peer_id, count } = &event {
                            let txs = {
                                let mut pool = mempool.lock().unwrap();
                                pool.peek_unannounced_for_peer(*peer_id, *count as usize)
                            };
                            if !txs.is_empty() {
                                let _ = commands
                                    .send(NetworkCommand::ProvideTxs {
                                        peer_id: *peer_id,
                                        txs,
                                    })
                                    .await;
                            }
                        }
                        // Drop per-peer advertised state when a peer goes away.
                        if let NetworkEvent::PeerDisconnected { peer_id, .. } = &event {
                            mempool.lock().unwrap().forget_peer(*peer_id);
                        }
                        record_network_event(&mut telem, &node_id, &event, &consensus).await;
                        if !consensus.handle_event(&event).await {
                            log_event(&node_id, &event);
                        }
                    }
                    None => {
                        warn!("coordinator channel closed");
                        break;
                    }
                }
            }
            Some(outcome) = validation_rx.recv() => {
                use validation::LedgerOutcome;
                if matches!(outcome, LedgerOutcome::Applied { .. }) {
                    telem.blocks_validated += 1;
                    telem.record(NodeEvent::BlockValidated {
                        node: node_id.clone(),
                        block_no: telem.blocks_validated,
                    }).await;
                }
                let rolled_back = consensus.on_validation_outcome(outcome).await;
                if rolled_back {
                    telem.record(NodeEvent::RolledBack {
                        node: node_id.clone(),
                        slot: telem.current_slot,
                    }).await;
                }
                for ev in consensus.drain_leios_telemetry() {
                    telem.record(ev).await;
                }
            }
            _ = stats_tick.tick(), if stats_interval > 0 => {
                telem.flush().await;
                let _ = commands.send(NetworkCommand::QueryPeers).await;
            }
            result = stdin_reader.read_line(&mut stdin_line) => {
                match result {
                    Ok(0) => {} // EOF — stdin closed, no more updates
                    Ok(_) => {
                        match serde_json::from_str::<config::DynamicConfigUpdate>(&stdin_line) {
                            Ok(update) => {
                                let mut current = dyn_tx.borrow().clone();
                                current.apply_update(&update);
                                let _ = dyn_tx.send(current);
                                info!(node_id = %node_id, "dynamic config updated");
                            }
                            Err(e) => {
                                warn!(node_id = %node_id, "invalid config update on stdin: {e}");
                            }
                        }
                        stdin_line.clear();
                    }
                    Err(e) => {
                        warn!(node_id = %node_id, "stdin read error: {e}");
                    }
                }
            }
            _ = &mut shutdown => {
                info!("shutting down");
                telem.flush().await;
                let _ = commands.send(NetworkCommand::Shutdown).await;
                break;
            }
        }
    }

    Ok(())
}

/// Record network events into telemetry.
async fn record_network_event(
    telem: &mut telemetry::TelemetryHandle,
    node_id: &str,
    event: &NetworkEvent,
    consensus: &consensus::Consensus,
) {
    match event {
        NetworkEvent::PeerConnected { peer_id, address } => {
            telem
                .record(NodeEvent::PeerConnected {
                    node: node_id.into(),
                    peer_id: peer_id.to_string(),
                    address: address.clone(),
                })
                .await;
        }
        NetworkEvent::PeerDisconnected { peer_id, reason } => {
            telem
                .record(NodeEvent::PeerDisconnected {
                    node: node_id.into(),
                    peer_id: peer_id.to_string(),
                    reason: reason.clone(),
                })
                .await;
        }
        NetworkEvent::TipAdvanced { tip, .. } => {
            telem.tip_block_no = Some(tip.block_no);
            telem.tip_hash = match &tip.point {
                net_core::types::Point::Specific { hash, .. } => {
                    Some(format!("{:02x}{:02x}", hash[30], hash[31]))
                }
                _ => None,
            };
            telem
                .record(NodeEvent::TipAdvanced {
                    node: node_id.into(),
                    block_no: tip.block_no,
                    slot: match &tip.point {
                        net_core::types::Point::Specific { slot, .. } => *slot,
                        _ => 0,
                    },
                })
                .await;
        }
        NetworkEvent::BlockReceived { .. } => {
            telem.blocks_received += 1;
            telem
                .record(NodeEvent::RBReceived {
                    node: node_id.into(),
                    slot: telem.current_slot,
                })
                .await;
        }
        NetworkEvent::TransactionReceived { .. } => {
            telem.txs_generated += 1;
        }
        NetworkEvent::PeerSnapshot { peers } => {
            let (chain_tree, tip_block_no, tip_hash) = consensus.chain_tree_snapshot();
            telem
                .emit_stats(peers, chain_tree, tip_block_no, tip_hash)
                .await;
        }
        NetworkEvent::LeiosBlockReceived { .. } => {
            telem
                .record(NodeEvent::EBReceived {
                    node: node_id.into(),
                    slot: telem.current_slot,
                })
                .await;
        }
        NetworkEvent::LeiosVotesReceived { ref vote_data, .. } => {
            telem
                .record(NodeEvent::VotesReceived {
                    node: node_id.into(),
                    count: vote_data.len(),
                })
                .await;
        }
        NetworkEvent::RolledBack { point, .. } => {
            telem
                .record(NodeEvent::RolledBack {
                    node: node_id.into(),
                    slot: match point {
                        net_core::types::Point::Specific { slot, .. } => *slot,
                        _ => 0,
                    },
                })
                .await;
        }
        _ => {}
    }
}

fn log_event(node_id: &str, event: &NetworkEvent) {
    match event {
        NetworkEvent::PeerConnected { peer_id, address } => {
            info!(node_id, %peer_id, %address, "peer connected");
        }
        NetworkEvent::PeerDisconnected { peer_id, reason } => {
            info!(node_id, %peer_id, %reason, "peer disconnected");
        }
        NetworkEvent::TransactionReceived { peer_id, body } => {
            // Accumulate received tx into local mempool for block inclusion.
            // (The tx was already received via TxSubmission from a peer.)
            info!(node_id, %peer_id, bytes = body.len(), "transaction received");
        }
        NetworkEvent::PeersDiscovered { peers, .. } => {
            info!(node_id, count = peers.len(), "peers discovered");
        }
        NetworkEvent::PeerSnapshot { .. } => {} // handled by telemetry
        _ => {
            info!(node_id, event = ?event, "network event");
        }
    }
}
