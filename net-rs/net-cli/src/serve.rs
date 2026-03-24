//! Fake Cardano node server: accepts connections and serves a synthetic
//! block chain generated on a Poisson distribution.
//!
//! Uses the multi-peer coordinator in responder-only mode. The block
//! generator injects blocks via `NetworkCommand::InjectBlock`.

use std::time::Duration;

use rand::rngs::StdRng;
use rand::{Rng, SeedableRng};
use tokio::sync::mpsc;

use net_core::peer::types::{NetworkCommand, NetworkEvent};
use net_core::peer::{spawn_coordinator, CoordinatorConfig};
use net_core::types::{BlockBody, Point, WrappedHeader};

/// Sample an exponential inter-arrival time: -ln(U) / λ
fn exp_sample(rng: &mut StdRng, rate: f64) -> Duration {
    let u: f64 = rng.gen_range(0.001..1.0);
    Duration::from_secs_f64(-u.ln() / rate)
}

/// Background task that generates blocks and occasional rollbacks on Poisson schedules.
async fn block_generator(
    commands: mpsc::Sender<NetworkCommand>,
    block_rate: f64,
    rollback_rate: f64,
    max_rollback_depth: usize,
) {
    let mut rng = StdRng::from_entropy();
    let mut next_slot: u64 = 1;
    let mut block_count: u64 = 0;

    loop {
        let block_interval = exp_sample(&mut rng, block_rate);
        let rollback_interval = if rollback_rate > 0.0 {
            exp_sample(&mut rng, rollback_rate)
        } else {
            Duration::from_secs(u64::MAX)
        };

        if rollback_interval < block_interval && block_count > 1 {
            tokio::time::sleep(rollback_interval).await;

            let max_depth = (block_count as usize - 1).min(max_rollback_depth);
            if max_depth == 0 {
                continue;
            }
            let depth = rng.gen_range(1..=max_depth);
            block_count = block_count.saturating_sub(depth as u64);
            // Roll back to origin for simplicity — the chain store handles truncation.
            let _ = commands
                .send(NetworkCommand::InjectRollback {
                    point: Point::Origin,
                })
                .await;
            println!("  rollback depth={depth} (#{block_count})");
        } else {
            tokio::time::sleep(block_interval).await;

            let slot = next_slot;
            next_slot += 1;

            let mut hash = [0u8; 32];
            rng.fill(&mut hash);

            let point = Point::Specific { slot, hash };

            let mut cbor_buf = Vec::new();
            let mut enc = minicbor::Encoder::new(&mut cbor_buf);
            enc.bytes(&hash).expect("CBOR encode");
            let header = WrappedHeader(cbor_buf.clone());
            let body = BlockBody(cbor_buf);

            let _ = commands
                .send(NetworkCommand::InjectBlock {
                    point: point.clone(),
                    header,
                    body,
                })
                .await;

            block_count += 1;
            println!("  generated block #{block_count} at slot {point}");
        }
    }
}

pub async fn run(
    port: u16,
    magic: u64,
    block_rate: f64,
    rollback_rate: f64,
    max_rollback_depth: usize,
) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
    let config = CoordinatorConfig {
        network_magic: magic,
        max_peers: 100,
        keepalive_interval: Duration::from_secs(20),
        sdu_timeout: Duration::from_secs(900),
        listen_address: Some(format!("0.0.0.0:{port}")),
        chain_store_capacity: 10_000,
    };

    let mut handle = spawn_coordinator(config);

    // Start block generator.
    let commands = handle.commands.clone();
    tokio::spawn(async move {
        block_generator(commands, block_rate, rollback_rate, max_rollback_depth).await;
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

    // Drain coordinator events (just log them).
    while let Some(event) = handle.events.recv().await {
        match event {
            NetworkEvent::PeerConnected { peer_id, address } => {
                println!("  {peer_id} connected: {address}");
            }
            NetworkEvent::PeerDisconnected { peer_id, reason } => {
                println!("  {peer_id} disconnected: {reason}");
            }
            NetworkEvent::TransactionReceived { peer_id, body } => {
                println!(
                    "  txsubmission: received tx from {peer_id} ({} bytes)",
                    body.len()
                );
            }
            _ => {}
        }
    }

    Ok(())
}
