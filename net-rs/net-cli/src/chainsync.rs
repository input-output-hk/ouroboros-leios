use net_core::mux::ProtocolConfig;
use net_core::protocol::Role;
use net_core::protocol::Runner;
use net_core::protocols::chainsync;
use net_core::protocols::chainsync::{ChainSync, ChainSyncEvent};
use net_core::types::Point;

use crate::connect;

pub async fn run(
    host: &str,
    magic: u64,
    count: usize,
) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
    let cs_proto = ProtocolConfig {
        id: chainsync::PROTOCOL_ID,
        priority: 1,
        ingress_limit: chainsync::INGRESS_LIMIT,
        egress_queue_size: 16,
    };

    println!("connecting to {host}...");
    let conn = connect::connect_and_handshake(host, magic, &[cs_proto]).await?;
    let running = conn.running;

    let (cs_send, cs_recv) = conn.channels.into_iter().next().expect("chainsync channel");

    let mut runner = Runner::<ChainSync>::new(Role::Client, cs_send, cs_recv);

    // Find intersection at origin.
    println!("finding intersection...");
    let result = chainsync::find_intersection(&mut runner, vec![Point::Origin]).await?;
    match &result {
        Some((point, tip)) => {
            println!("intersection found: {point}  tip: {tip}");
        }
        None => {
            println!("no intersection found (unexpected for origin)");
            running.abort();
            return Ok(());
        }
    }

    // Follow the chain.
    println!("following chain ({count} headers)...");
    for i in 0..count {
        let event = chainsync::request_next(&mut runner).await?;
        match event {
            ChainSyncEvent::RollForward { header, tip } => {
                println!(
                    "  [{:>4}] roll forward  header={} bytes  tip={}",
                    i + 1,
                    header.0.len(),
                    tip,
                );
            }
            ChainSyncEvent::RollBackward { point, tip } => {
                println!("  [{:>4}] roll backward to {point}  tip={tip}", i + 1);
            }
        }
    }

    // Clean shutdown.
    chainsync::done(&mut runner).await?;
    running.abort();
    println!("done");
    Ok(())
}
