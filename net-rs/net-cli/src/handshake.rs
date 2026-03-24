use std::net::ToSocketAddrs;

use net_core::bearer::tcp::TcpBearer;
use net_core::codec::{CodecRecv, CodecSend};
use net_core::mux::scheduler::RoundRobin;
use net_core::mux::{Mux, MuxConfig, ProtocolConfig, MODE_INITIATOR};
use net_core::protocols::handshake;
use net_core::protocols::handshake::n2n;

pub async fn run(host: &str, magic: u64) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
    let addr = host
        .to_socket_addrs()?
        .next()
        .ok_or_else(|| format!("could not resolve {host}"))?;

    println!("connecting to {addr}...");

    let bearer = TcpBearer::connect(addr).await?;
    println!("connected, starting handshake...");

    let proto = ProtocolConfig {
        id: handshake::PROTOCOL_ID,
        priority: 0,
        ingress_limit: handshake::SIZE_LIMIT,
        egress_queue_size: 4,
    };

    let mut mux = Mux::new(MuxConfig::default(), RoundRobin::default(), MODE_INITIATOR);
    let (send_ch, recv_ch) = mux.register(&proto);
    let running = mux.run(bearer);

    let versions = n2n::version_table(&n2n::VersionData {
        network_magic: magic,
        initiator_only_diffusion_mode: false,
        peer_sharing: 0,
        query: false,
    });

    let result =
        handshake::run_client(CodecSend::new(send_ch), CodecRecv::new(recv_ch), versions).await;

    match &result {
        Ok(handshake::HandshakeResult::Accepted {
            version_number,
            params,
        }) => {
            println!("handshake accepted: version {version_number}");
            match n2n::VersionData::decode(params) {
                Ok(data) => println!("  negotiated: {data:?}"),
                Err(e) => println!("  (could not decode params: {e})"),
            }
        }
        Ok(handshake::HandshakeResult::Refused(reason)) => {
            println!("handshake refused: {reason:?}");
        }
        Ok(handshake::HandshakeResult::QueryReply(table)) => {
            println!("query reply: {} versions", table.len());
            for v in table.keys() {
                println!("  version {v}");
            }
        }
        Err(e) => {
            println!("handshake error: {e}");
        }
    }

    running.abort();
    Ok(())
}
