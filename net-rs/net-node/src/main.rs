mod clock;
mod config;
mod network;

use clap::Parser;
use net_core::multi_peer::types::NetworkEvent;
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
        "starting node"
    );

    let mut slot_clock = clock::SlotClock::new(config.genesis_time_unix, config.slot_duration_ms);
    let mut handle = network::start(&config).await?;

    // Graceful shutdown on Ctrl-C.
    let shutdown = tokio::signal::ctrl_c();
    tokio::pin!(shutdown);

    loop {
        tokio::select! {
            slot = slot_clock.tick() => {
                info!(slot, node_id = %config.node_id, "slot tick");
            }
            event = handle.events.recv() => {
                match event {
                    Some(event) => log_event(&config.node_id, &event),
                    None => {
                        warn!("coordinator channel closed");
                        break;
                    }
                }
            }
            _ = &mut shutdown => {
                info!("shutting down");
                let _ = handle.commands.send(
                    net_core::multi_peer::types::NetworkCommand::Shutdown
                ).await;
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
        NetworkEvent::TipAdvanced { tip, .. } => {
            info!(node_id, %tip, "tip advanced");
        }
        NetworkEvent::RolledBack { point, tip } => {
            info!(node_id, to = %point, %tip, "rolled back");
        }
        NetworkEvent::BlockReceived { point, .. } => {
            info!(node_id, %point, "block received");
        }
        NetworkEvent::TransactionReceived { peer_id, body } => {
            info!(node_id, %peer_id, bytes = body.len(), "transaction received");
        }
        NetworkEvent::PeersDiscovered { peers, .. } => {
            info!(node_id, count = peers.len(), "peers discovered");
        }
        _ => {
            // Leios events and others -- log generically for now.
            info!(node_id, event = ?event, "network event");
        }
    }
}
