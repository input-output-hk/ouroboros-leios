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
            let header = WrappedHeader::opaque(cbor_buf.clone());
            let body = BlockBody::opaque(cbor_buf);

            let _ = commands
                .send(NetworkCommand::InjectBlock {
                    point: point.clone(),
                    header: Box::new(header),
                    body,
                })
                .await;

            block_count += 1;
            println!("  generated block #{block_count} at slot {point}");
        }
    }
}

/// Background task that generates Leios endorser blocks and votes on a Poisson schedule.
/// Generates one EB per Praos block (roughly), plus votes for each EB.
async fn leios_generator(commands: mpsc::Sender<NetworkCommand>, rate: f64) {
    let mut rng = StdRng::from_entropy();
    let mut next_eb_slot: u64 = 1;

    loop {
        let interval = exp_sample(&mut rng, rate);
        tokio::time::sleep(interval).await;

        let slot = next_eb_slot;
        next_eb_slot += 1;

        let mut hash = [0u8; 32];
        rng.fill(&mut hash);

        // Inject a fake endorser block.
        let block_data = vec![0x82, slot as u8, 0x00]; // minimal CBOR
        let _ = commands
            .send(NetworkCommand::InjectLeiosBlock {
                point: net_core::types::Point::Specific { slot, hash },
                block: block_data,
            })
            .await;

        // Inject some votes for this EB.
        let num_votes = rng.gen_range(1..=3u8);
        let mut vote_ids = Vec::new();
        let mut vote_data = Vec::new();
        for v in 0..num_votes {
            vote_ids.push((slot, vec![v]));
            vote_data.push(vec![0xA0, v]); // minimal CBOR
        }
        let _ = commands
            .send(NetworkCommand::InjectLeiosVotes {
                votes: vote_ids,
                data: vote_data,
            })
            .await;

        println!("  leios: generated EB at slot {slot} ({num_votes} votes)");
    }
}

pub async fn run(
    port: u16,
    magic: u64,
    block_rate: f64,
    rollback_rate: f64,
    max_rollback_depth: usize,
    leios: bool,
) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
    let config = CoordinatorConfig {
        network_magic: magic,
        max_peers: 100,
        keepalive_interval: Duration::from_secs(20),
        sdu_timeout: Duration::from_secs(900),
        listen_address: Some(format!("0.0.0.0:{port}")),
        chain_store_capacity: 10_000,
        duplex: false,
        leios_enabled: leios,
        leios_dedup_window: 1000,
    };

    let mut handle = spawn_coordinator(config);

    // Start block generator.
    let commands = handle.commands.clone();
    tokio::spawn(async move {
        block_generator(commands, block_rate, rollback_rate, max_rollback_depth).await;
    });

    // Start Leios generator if enabled.
    if leios {
        let commands = handle.commands.clone();
        tokio::spawn(async move {
            leios_generator(commands, block_rate * 2.0).await;
        });
    }

    let rollback_info = if rollback_rate > 0.0 {
        format!(", rollback rate={rollback_rate}/sec")
    } else {
        String::new()
    };
    let leios_info = if leios { ", leios=on" } else { "" };
    println!(
        "fake server listening on port {port} (magic={magic}, block rate={block_rate}/sec (~{:.0}s mean){rollback_info}{leios_info})",
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
