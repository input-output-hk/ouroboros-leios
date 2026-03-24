//! PeerSharing CLI command: request peers from a Cardano node.
//!
//! Requires the node to support PeerSharing (peer_sharing=1 in handshake).

use std::net::ToSocketAddrs;

use net_core::bearer::tcp::TcpBearer;
use net_core::codec::{CodecRecv, CodecSend};
use net_core::mux::scheduler::RoundRobin;
use net_core::mux::{Mux, MuxConfig, ProtocolConfig, MODE_INITIATOR};
use net_core::protocol::Role;
use net_core::protocol::Runner;
use net_core::protocols::handshake;
use net_core::protocols::handshake::n2n;
use net_core::protocols::peersharing;
use net_core::protocols::peersharing::PeerSharing;

pub async fn run(host: &str, magic: u64, amount: u8) -> Result<(), Box<dyn std::error::Error>> {
    println!("connecting to {host}...");

    let addr = host
        .to_socket_addrs()?
        .next()
        .ok_or_else(|| format!("could not resolve {host}"))?;

    let bearer = TcpBearer::connect(addr).await?;

    let hs_proto = ProtocolConfig {
        id: handshake::PROTOCOL_ID,
        priority: 0,
        ingress_limit: handshake::SIZE_LIMIT,
        egress_queue_size: 4,
    };
    let ps_proto = ProtocolConfig {
        id: peersharing::PROTOCOL_ID,
        priority: 5,
        ingress_limit: peersharing::INGRESS_LIMIT,
        egress_queue_size: 4,
    };
    let mut mux = Mux::new(MuxConfig::default(), RoundRobin::default(), MODE_INITIATOR);
    let (hs_send, hs_recv) = mux.register(&hs_proto);
    let (ps_send, ps_recv) = mux.register(&ps_proto);

    let running = mux.run(bearer);

    // Handshake with peer_sharing = 1 to enable PeerSharing protocol.
    let versions = n2n::version_table(&n2n::VersionData {
        network_magic: magic,
        initiator_only_diffusion_mode: false,
        peer_sharing: 1,
        query: false,
    });

    let hs_result =
        handshake::run_client(CodecSend::new(hs_send), CodecRecv::new(hs_recv), versions).await;

    match hs_result {
        Ok(handshake::HandshakeResult::Accepted {
            version_number,
            params,
        }) => {
            println!("  handshake accepted: version {version_number}");
            if let Ok(vd) = minicbor::decode::<n2n::VersionData>(&params) {
                if vd.peer_sharing == 0 {
                    running.abort();
                    return Err("node does not support peer sharing (peer_sharing=0)".into());
                }
                println!("  peer sharing enabled");
            }
        }
        Ok(handshake::HandshakeResult::Refused(reason)) => {
            running.abort();
            return Err(format!("handshake refused: {reason:?}").into());
        }
        Ok(handshake::HandshakeResult::QueryReply(_)) => {
            running.abort();
            return Err("unexpected query reply".into());
        }
        Err(e) => {
            running.abort();
            return Err(e.into());
        }
    }

    let mut runner = Runner::<PeerSharing>::new(
        Role::Client,
        CodecSend::new(ps_send),
        CodecRecv::new(ps_recv),
    );

    println!("requesting {amount} peers...");
    let peers = peersharing::share_request(&mut runner, amount).await?;

    if peers.is_empty() {
        println!("  no peers returned");
    } else {
        println!("  received {} peer(s):", peers.len());
        for peer in &peers {
            println!("    {peer}");
        }
    }

    peersharing::done(&mut runner).await?;
    running.abort();
    println!("done");
    Ok(())
}
