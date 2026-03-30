mod clock;
mod config;
mod consensus;
mod mempool;
mod network;
mod production;
mod validation;

use clap::Parser;
use net_core::multi_peer::types::{NetworkCommand, NetworkEvent};
use tracing::{info, warn};

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
    let mut handle = network::start(&config).await?;
    let commands = handle.commands.clone();

    // Block producer.
    let mut producer = production::BlockProducer::new(&config.production, config.seed);
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

    // Validator and consensus.
    let (validator, mut validation_rx) = validation::Validator::new(config.validation.clone());
    let mut consensus =
        consensus::Consensus::new(config.node_id.clone(), commands.clone(), validator);

    // Transaction generator (background task).
    let _tx_handle = mempool::spawn_tx_generator(
        &config.transactions,
        config.seed,
        commands.clone(),
        config.node_id.clone(),
    );

    // Graceful shutdown on Ctrl-C.
    let shutdown = tokio::signal::ctrl_c();
    tokio::pin!(shutdown);

    let leios = config.leios_enabled;

    loop {
        tokio::select! {
            slot = slot_clock.tick() => {
                // Praos: try to produce a ranking block.
                if let Some((point, header, body)) = producer.try_produce_block(slot) {
                    info!(
                        node_id = %config.node_id,
                        %point,
                        block_count = producer.block_count(),
                        "produced block"
                    );
                    consensus.register_self_produced(&point);
                    let _ = commands.send(NetworkCommand::InjectBlock {
                        point,
                        header: Box::new(header),
                        body,
                    }).await;
                }

                // Leios: produce EBs and votes at stage boundaries.
                if leios && producer.is_stage_boundary(slot) {
                    if let Some(eb) = producer.try_produce_eb(slot) {
                        info!(
                            node_id = %config.node_id,
                            %eb.point,
                            "produced endorser block"
                        );
                        let _ = commands.send(NetworkCommand::InjectLeiosBlock {
                            point: eb.point,
                            block: eb.data,
                        }).await;
                    }
                    if let Some(votes) = producer.try_produce_votes(slot) {
                        info!(
                            node_id = %config.node_id,
                            count = votes.vote_ids.len(),
                            "produced votes"
                        );
                        let _ = commands.send(NetworkCommand::InjectLeiosVotes {
                            votes: votes.vote_ids,
                            data: votes.vote_data,
                        }).await;
                    }
                }
            }
            event = handle.events.recv() => {
                match event {
                    Some(event) => {
                        if !consensus.handle_event(&event).await {
                            log_event(&config.node_id, &event);
                        }
                    }
                    None => {
                        warn!("coordinator channel closed");
                        break;
                    }
                }
            }
            Some(result) = validation_rx.recv() => {
                consensus.on_validation_complete(result).await;
            }
            _ = &mut shutdown => {
                info!("shutting down");
                let _ = commands.send(NetworkCommand::Shutdown).await;
                break;
            }
        }
    }

    Ok(())
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
            info!(node_id, %peer_id, bytes = body.len(), "transaction received");
        }
        NetworkEvent::PeersDiscovered { peers, .. } => {
            info!(node_id, count = peers.len(), "peers discovered");
        }
        _ => {
            info!(node_id, event = ?event, "network event");
        }
    }
}
