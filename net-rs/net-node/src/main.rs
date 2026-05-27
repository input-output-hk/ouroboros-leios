mod clock;
mod config;
mod consensus;
mod mempool;
mod network;
mod production;
mod telemetry;
mod validation;

// Use jemalloc for better behavior under heavy small-allocation churn
// (tx body clones, mux Bytes traffic). glibc's allocator tends to hold
// freed pages, inflating RSS even after the heap shrinks; jemalloc
// returns memory to the OS more aggressively.
#[global_allocator]
static GLOBAL: tikv_jemallocator::Jemalloc = tikv_jemallocator::Jemalloc;

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

    // Shared per-peer RTT cache.  The coordinator's keepalive task
    // writes measurements via the observer callback below; the
    // consensus state machines read at fetch-decision time.
    let rtt_cache = shared_consensus::fetch::PeerRttCache::new();
    let peer_rtt_observer: net_core::multi_peer::PeerRttObserver = {
        let cache = rtt_cache.clone();
        std::sync::Arc::new(move |pid, rtt| {
            let con_pid = shared_consensus::peer::PeerId(pid.0);
            match rtt {
                Some(d) => cache.set(con_pid, d),
                None => cache.forget(con_pid),
            }
        })
    };

    // Materialise the per-node behaviour handle once and share clones
    // with the coordinator (for the per-peer outbound transform path)
    // and the consensus state machines (for reactive + decision hooks).
    let behaviour_seed = config
        .seed
        .unwrap_or_else(|| shared_consensus::behaviour::seed_from_node_id(&config.node_id));
    let behaviour_spec = config
        .behaviour
        .clone()
        .unwrap_or(shared_consensus::behaviour::BehaviourSpec::Honest);
    info!(?behaviour_spec, behaviour_seed, "materialising per-node behaviour");
    let behaviour_handle =
        shared_consensus::behaviour::build_handle(&behaviour_spec, behaviour_seed);

    let mut handle = network::start(
        &config,
        Some(tx_body_resolver),
        Some(peer_rtt_observer),
        Some(behaviour_handle.clone()),
    )
    .await?;
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
        rtt_cache,
        config.fetch_policy,
        behaviour_handle.clone(),
        behaviour_spec.clone(),
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

    // State-size diagnostic logging is gated by config; 0 = off.
    let state_size_log_every_n_ticks = config.telemetry.state_sizes_log_every_n_ticks;
    let mut state_size_tick: u64 = 0;

    // Graceful shutdown on Ctrl-C.
    let shutdown = tokio::signal::ctrl_c();
    tokio::pin!(shutdown);

    // Stdin reader for dynamic config updates from net-cluster.
    let stdin = tokio::io::stdin();
    let mut stdin_reader = tokio::io::BufReader::new(stdin);
    let mut stdin_line = String::new();

    let leios = config.leios_enabled;
    let node_id = config.node_id.clone();

    // Pull the mempool's admit notifier and tracked peer set.  Each
    // successful mempool admit fires the notify; the select! arm below
    // fans the new txs out to every connected peer via `ProvideTxs`.
    // Without this push-on-admit signal, txsubmission's pull cadence
    // can stall after the startup flurry — the consumer settles into a
    // non-blocking poll loop, the provider's per-peer channel runs dry
    // mid-cycle, and the natural `TxsRequested` wakeup never re-fires.
    let mut admit_rx = mempool
        .lock()
        .unwrap()
        .take_admit_rx()
        .expect("admit_rx already taken");
    let mut connected_peers: std::collections::BTreeSet<net_core::peer::PeerId> =
        std::collections::BTreeSet::new();

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
                let certified_eb_slot = if leios { consensus.cert_for_parent() } else { None };
                let certified_eb = certified_eb_slot.is_some();
                if let Some(produced) = producer.try_produce_block(slot, prev_hash, next_block_no, certified_eb, &mempool, consensus.leios_state()) {
                    // Consult the per-node behaviour: an adversarial
                    // `Suppress` drops the win silently; `Equivocate`
                    // produces a duplicate RB with the same issuer +
                    // slot but a different body, triggering CIP-0164
                    // detection on every honest peer.
                    use shared_consensus::behaviour::RbProductionStrategy;
                    let strategy = consensus.rb_production_strategy(slot);
                    if strategy == RbProductionStrategy::Suppress {
                        info!(
                            node_id = %node_id,
                            slot,
                            "suppressing produced RB (behaviour=suppress)"
                        );
                    } else {
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
                    // Tx bodies are already pinned in the mempool by
                    // `BlockProducer::try_produce_block` via
                    // `Mempool::produce_eb`; the LeiosStore serves them
                    // through its `TxBodyResolver` fallback.
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
                        consensus
                            .register_self_produced_eb(eb.point.clone(), &eb.data)
                            .await;
                    }

                    // For Equivocate{ways}: build the variants and
                    // hand them to the behaviour BEFORE
                    // `register_self_produced` fires the ChainStore
                    // subscription.  Otherwise serve_chainsync wakes
                    // and reads the primary while the behaviour's
                    // variant map is still empty, so transform_outbound
                    // returns Send and the substitution is missed.
                    if let RbProductionStrategy::Equivocate { ways } = strategy {
                        use shared_consensus::behaviour::RbVariantInput;
                        let mut variant_records: Vec<RbVariantInput> =
                            Vec::with_capacity(ways as usize);
                        let primary_hash = match &produced.point {
                            net_core::types::Point::Specific { hash, .. } => *hash,
                            net_core::types::Point::Origin => [0u8; 32],
                        };
                        variant_records.push(RbVariantInput {
                            hash: primary_hash,
                            header: produced.header.raw.clone(),
                            body: produced.body.raw.clone(),
                        });
                        for i in 1..ways {
                            let extra = producer.produce_equivocation_extra(
                                &produced,
                                prev_hash,
                                next_block_no,
                            );
                            let extra_hash = match &extra.point {
                                net_core::types::Point::Specific { hash, .. } => *hash,
                                net_core::types::Point::Origin => [0u8; 32],
                            };
                            info!(
                                node_id = %node_id,
                                primary = %produced.point,
                                extra = %extra.point,
                                variant = i,
                                "produced equivocation variant RB"
                            );
                            telem.record(NodeEvent::RBGenerated {
                                node: node_id.clone(),
                                slot,
                                size_bytes: extra.body.raw.len(),
                            }).await;
                            variant_records.push(RbVariantInput {
                                hash: extra_hash,
                                header: extra.header.raw.clone(),
                                body: extra.body.raw.clone(),
                            });
                        }
                        {
                            let mut guard = behaviour_handle
                                .lock()
                                .expect("behaviour mutex poisoned");
                            guard.record_rb_variants(slot, &variant_records);
                        }
                    }

                    consensus
                        .register_self_produced(&produced.point, &produced.header, &produced.body)
                        .await;
                    }
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
                            // Pin the bodies in the mempool synchronously
                            // so the next on_slot's MissingTX predicate sees
                            // them — the validator pipeline still runs for
                            // ledger-validity checking, but the predicate
                            // is content-addressed and doesn't need to wait.
                            {
                                let mut pool = mempool.lock().unwrap();
                                for body in &outcome.matched_bodies {
                                    pool.merge_eb_body(body.clone());
                                }
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
                        // Maintain the per-peer fanout set.
                        if let NetworkEvent::PeerConnected { peer_id, .. } = &event {
                            connected_peers.insert(*peer_id);
                        }
                        // Drop per-peer advertised state when a peer goes away.
                        if let NetworkEvent::PeerDisconnected { peer_id, .. } = &event {
                            connected_peers.remove(peer_id);
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
            Some(admitted) = admit_rx.recv() => {
                // A tx just entered the free pool (locally generated or
                // peer-received-and-validated).  Announce it to every
                // connected peer that hasn't already been told,
                // O(log N) per peer via `mark_announced_to_peer`.
                let peer_ids: Vec<_> = connected_peers.iter().copied().collect();
                for peer_id in peer_ids {
                    let should_send = {
                        let mut pool = mempool.lock().unwrap();
                        pool.mark_announced_to_peer(peer_id, &admitted.tx_id)
                    };
                    if should_send {
                        let _ = commands
                            .send(NetworkCommand::ProvideTxs {
                                peer_id,
                                txs: vec![admitted.clone()],
                            })
                            .await;
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
                if state_size_log_every_n_ticks > 0 {
                    state_size_tick = state_size_tick.wrapping_add(1);
                    if state_size_tick % state_size_log_every_n_ticks == 0 {
                        consensus.log_state_sizes();
                        mempool.lock().expect("mempool mutex poisoned").as_inner()
                            .log_state_sizes(&node_id);
                    }
                }
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
                                // Behaviour swap is separate from the
                                // watch-channel ambient config: it
                                // mutates the live state machines.
                                if let Some(spec) = &update.behaviour {
                                    consensus.set_behaviour(spec, &mempool);
                                } else if matches!(update.behaviour_reset, Some(true)) {
                                    consensus.reset_behaviour(&mempool);
                                }
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
            tracing::debug!(node_id, %peer_id, bytes = body.len(), "transaction received");
        }
        NetworkEvent::PeersDiscovered { peers, .. } => {
            info!(node_id, count = peers.len(), "peers discovered");
        }
        NetworkEvent::PeerSnapshot { .. } => {} // handled by telemetry
        _ => {
            tracing::debug!(node_id, event = ?event, "network event");
        }
    }
}
