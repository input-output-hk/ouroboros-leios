//! Multi-peer chain follower: connects to N nodes via the coordinator
//! and prints aggregated chain events.

use std::time::{Duration, Instant};

use net_core::multi_peer::types::{NetworkCommand, NetworkEvent};
use net_core::multi_peer::{spawn_coordinator, CoordinatorConfig};

#[allow(clippy::too_many_arguments)]
pub async fn run(
    hosts: &[String],
    magic: u64,
    max_peers: usize,
    listen: Option<String>,
    duplex: bool,
    leios: bool,
    max_handshaking: usize,
    max_connections_per_ip: usize,
    scheduler_args: &crate::scheduler_args::SchedulerArgs,
) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
    if hosts.is_empty() && listen.is_none() {
        return Err("at least one --host or --listen is required".into());
    }

    let config = CoordinatorConfig {
        network_magic: magic,
        max_peers,
        keepalive_interval: Duration::from_secs(20),
        sdu_timeout: Duration::from_secs(900),
        listen_address: listen.clone(),
        chain_store_capacity: 2160,
        duplex,
        leios_enabled: leios,
        leios_dedup_window: 1000,
        traffic_class_overrides: scheduler_args.traffic_class_overrides()?,
        scheduler_type: scheduler_args.scheduler,
        max_handshaking,
        max_connections_per_ip,
        peer_delays: std::collections::HashMap::new(),
    };

    let mut handle = spawn_coordinator(config);

    // Add initial peers.
    for host in hosts {
        handle
            .commands
            .send(NetworkCommand::AddPeer {
                address: host.clone(),
            })
            .await?;
    }

    let listen_info = listen
        .map(|a| format!(", listening on {a}"))
        .unwrap_or_default();
    println!(
        "following chain from {} peer(s){listen_info}...",
        hosts.len()
    );
    let mut last_block_time = Instant::now();

    // Event loop.
    while let Some(event) = handle.events.recv().await {
        match event {
            NetworkEvent::PeerConnected { peer_id, address } => {
                println!("  {peer_id} connected: {address}");
            }
            NetworkEvent::PeerDisconnected { peer_id, reason } => {
                println!("  {peer_id} disconnected: {reason}");
            }
            NetworkEvent::TipAdvanced { tip, .. } => {
                let elapsed = last_block_time.elapsed();
                last_block_time = Instant::now();
                println!(
                    "  block #{:<8} {}  +{:.1}s",
                    tip.block_no,
                    tip.point,
                    elapsed.as_secs_f64(),
                );
            }
            NetworkEvent::RolledBack { point, tip } => {
                println!("  rollback to {point}  tip: {tip}");
            }
            NetworkEvent::BlockReceived { point, body } => {
                println!("  block received: {} ({} bytes)", point, body.raw.len());
            }
            NetworkEvent::PeersDiscovered { peers } => {
                println!("  discovered {} peer(s):", peers.len());
                for peer in &peers {
                    println!("    {peer}");
                }
            }
            NetworkEvent::TransactionReceived { peer_id, body } => {
                println!("  tx received from {peer_id} ({} bytes)", body.len());
            }
            NetworkEvent::LeiosBlockAnnounced { .. } => {
                println!("  leios: EB announced via RB header");
            }
            NetworkEvent::LeiosBlockOffered { point } => {
                println!("  leios: EB offered at {point}");
            }
            NetworkEvent::LeiosBlockTxsOffered { point } => {
                println!("  leios: EB transactions offered at {point}");
            }
            NetworkEvent::LeiosVotesOffered { votes } => {
                println!("  leios: {} vote(s) offered", votes.len());
            }
            NetworkEvent::LeiosBlockReceived { point, block } => {
                println!("  leios: EB received at {point} ({} bytes)", block.len());
            }
            NetworkEvent::LeiosVotesReceived { votes } => {
                println!("  leios: {} vote(s) received", votes.len());
            }
            NetworkEvent::LeiosBlockTxsReceived {
                point,
                transactions,
            } => {
                println!(
                    "  leios: EB txs received at {point} ({} txs)",
                    transactions.len()
                );
            }
            NetworkEvent::BlockFetchFailed { from, to } => {
                if from == to {
                    println!("  block fetch failed: {from}");
                } else {
                    println!("  block fetch failed: {from}..{to}");
                }
            }
        }
    }

    Ok(())
}
