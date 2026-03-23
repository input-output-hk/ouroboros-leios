use std::net::ToSocketAddrs;

use net_core::bearer::tcp::TcpBearer;
use net_core::codec::{CodecRecv, CodecSend};
use net_core::mux::scheduler::RoundRobin;
use net_core::mux::{Mux, MuxConfig, ProtocolConfig, MODE_INITIATOR};
use net_core::protocol::Role;
use net_core::protocol::Runner;
use net_core::protocols::blockfetch;
use net_core::protocols::blockfetch::BlockFetch;
use net_core::protocols::chainsync;
use net_core::protocols::chainsync::ChainSync;
use net_core::protocols::handshake;
use net_core::protocols::handshake::n2n;
use net_core::types::Point;

pub async fn run(host: &str, magic: u64) -> Result<(), Box<dyn std::error::Error>> {
    let addr = host
        .to_socket_addrs()?
        .next()
        .ok_or_else(|| format!("could not resolve {host}"))?;

    println!("connecting to {addr}...");
    let bearer = TcpBearer::connect(addr).await?;
    println!("connected");

    // Register handshake, chainsync, and blockfetch on the mux.
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
    let bf_proto = ProtocolConfig {
        id: blockfetch::PROTOCOL_ID,
        priority: 2,
        ingress_limit: blockfetch::INGRESS_LIMIT,
        egress_queue_size: 16,
    };

    let mut mux = Mux::new(MuxConfig::default(), RoundRobin::default(), MODE_INITIATOR);
    let (hs_send, hs_recv) = mux.register(&hs_proto);
    let (cs_send, cs_recv) = mux.register(&cs_proto);
    let (bf_send, bf_recv) = mux.register(&bf_proto);
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

    // ChainSync: find the tip so we have a point for BlockFetch.
    let mut cs_runner = Runner::<ChainSync>::new(
        Role::Client,
        CodecSend::new(cs_send),
        CodecRecv::new(cs_recv),
    );

    println!("finding intersection...");
    let result = chainsync::find_intersection(&mut cs_runner, vec![Point::Origin]).await?;
    let tip = match result {
        Some((_point, tip)) => {
            println!("intersection found, tip: {tip}");
            tip
        }
        None => {
            println!("no intersection found");
            running.abort();
            return Ok(());
        }
    };

    // Use the tip point for a single-block BlockFetch request.
    let fetch_point = tip.point.clone();
    if fetch_point == Point::Origin {
        println!("tip is origin, nothing to fetch");
        chainsync::done(&mut cs_runner).await?;
        running.abort();
        return Ok(());
    }

    println!("fetching block at {fetch_point}...");

    let mut bf_runner = Runner::<BlockFetch>::new(
        Role::Client,
        CodecSend::new(bf_send),
        CodecRecv::with_max_buffer(bf_recv, blockfetch::SIZE_LIMIT_STREAMING),
    );

    let has_blocks =
        blockfetch::request_range(&mut bf_runner, fetch_point.clone(), fetch_point).await?;

    if has_blocks {
        let mut block_count = 0u64;
        while let Some(body) = blockfetch::recv_block(&mut bf_runner).await? {
            block_count += 1;
            println!(
                "  block #{block_count}: {} bytes  tip={}",
                body.0.len(),
                tip,
            );
        }
        println!("batch complete: {block_count} block(s)");
    } else {
        println!("server has no blocks for requested range");
    }

    // Clean shutdown.
    blockfetch::done(&mut bf_runner).await?;
    chainsync::done(&mut cs_runner).await?;
    running.abort();
    println!("done");
    Ok(())
}
