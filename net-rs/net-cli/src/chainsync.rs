use std::net::ToSocketAddrs;

use net_core::bearer::tcp::TcpBearer;
use net_core::codec::{CodecRecv, CodecSend};
use net_core::mux::scheduler::RoundRobin;
use net_core::mux::{Mux, MuxConfig, ProtocolConfig, MODE_INITIATOR};
use net_core::protocol::Role;
use net_core::protocol::Runner;
use net_core::protocols::chainsync;
use net_core::protocols::chainsync::{ChainSync, ChainSyncEvent};
use net_core::protocols::handshake;
use net_core::protocols::handshake::n2n;
use net_core::types::Point;

pub async fn run(host: &str, magic: u64, count: usize) -> Result<(), Box<dyn std::error::Error>> {
    let addr = host
        .to_socket_addrs()?
        .next()
        .ok_or_else(|| format!("could not resolve {host}"))?;

    println!("connecting to {addr}...");
    let bearer = TcpBearer::connect(addr).await?;
    println!("connected");

    // Register both handshake and chainsync on the mux.
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

    let mut mux = Mux::new(MuxConfig::default(), RoundRobin::default(), MODE_INITIATOR);
    let (hs_send, hs_recv) = mux.register(&hs_proto);
    let (cs_send, cs_recv) = mux.register(&cs_proto);
    let running = mux.run(bearer);

    // Handshake.
    let versions = n2n::version_table(&n2n::VersionData {
        network_magic: magic,
        initiator_only_diffusion_mode: false,
        peer_sharing: 0,
        query: false,
    });

    let hs_result =
        handshake::run_client(CodecSend::new(hs_send), CodecRecv::new(hs_recv), versions).await?;

    match &hs_result {
        handshake::HandshakeResult::Accepted { version_number, .. } => {
            println!("handshake accepted: version {version_number}");
        }
        handshake::HandshakeResult::Refused(reason) => {
            println!("handshake refused: {reason:?}");
            running.abort();
            return Ok(());
        }
        handshake::HandshakeResult::QueryReply(_) => {
            println!("unexpected query reply");
            running.abort();
            return Ok(());
        }
    }

    // ChainSync.
    let mut runner = Runner::<ChainSync>::new(
        Role::Client,
        CodecSend::new(cs_send),
        CodecRecv::new(cs_recv),
    );

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
