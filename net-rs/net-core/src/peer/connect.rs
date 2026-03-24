//! Connection helpers: TCP connect/accept → mux setup → handshake.
//!
//! These functions establish a multiplexed, handshaked connection to a
//! Cardano node. They are used by both the CLI tools and the coordinator.

use std::net::ToSocketAddrs;

use crate::bearer::tcp::TcpBearer;
use crate::codec::{CodecRecv, CodecSend};
use crate::mux::scheduler::RoundRobin;
use crate::mux::{Mux, MuxConfig, ProtocolConfig, RunningMux, MODE_INITIATOR, MODE_RESPONDER};
use crate::protocols::handshake;
use crate::protocols::handshake::n2n;

/// A live mux connection with handshake completed.
pub struct Connection {
    pub running: RunningMux,
    pub channels: Vec<(CodecSend, CodecRecv)>,
}

/// A duplex connection with separate channel sets for initiator and responder.
pub struct DuplexConnection {
    pub running: RunningMux,
    /// Channels for initiator-direction protocols (we act as client).
    pub initiator_channels: Vec<(CodecSend, CodecRecv)>,
    /// Channels for responder-direction protocols (we act as server).
    pub responder_channels: Vec<(CodecSend, CodecRecv)>,
}

/// Connect to a Cardano node, set up the mux with the given protocols,
/// and perform the version handshake. Returns the running mux and
/// codec pairs for each protocol (in registration order, excluding handshake).
pub async fn connect_and_handshake(
    host: &str,
    magic: u64,
    protocols: &[ProtocolConfig],
) -> Result<Connection, Box<dyn std::error::Error + Send + Sync>> {
    connect_and_handshake_with_config(host, magic, protocols, MuxConfig::default()).await
}

/// Like `connect_and_handshake` but with a custom mux config.
pub async fn connect_and_handshake_with_config(
    host: &str,
    magic: u64,
    protocols: &[ProtocolConfig],
    mux_config: MuxConfig,
) -> Result<Connection, Box<dyn std::error::Error + Send + Sync>> {
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

    let mut mux = Mux::new(mux_config, RoundRobin::default(), MODE_INITIATOR);
    let (hs_send, hs_recv) = mux.register(&hs_proto);

    let mut channels = Vec::new();
    for proto in protocols {
        let (send, recv) = mux.register(proto);
        channels.push((CodecSend::new(send), CodecRecv::new(recv)));
    }

    let running = mux.run(bearer);

    let versions = n2n::version_table(&n2n::VersionData {
        network_magic: magic,
        initiator_only_diffusion_mode: false,
        peer_sharing: 0,
        query: false,
    });

    let hs_result =
        handshake::run_client(CodecSend::new(hs_send), CodecRecv::new(hs_recv), versions).await;

    match hs_result {
        Ok(handshake::HandshakeResult::Accepted { version_number, .. }) => {
            tracing::info!("handshake accepted: version {version_number}");
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

    Ok(Connection { running, channels })
}

/// Accept a connection and perform the server-side handshake.
pub async fn accept_and_handshake(
    listener: &tokio::net::TcpListener,
    magic: u64,
    protocols: &[ProtocolConfig],
    mux_config: MuxConfig,
) -> Result<Connection, Box<dyn std::error::Error + Send + Sync>> {
    let (bearer, peer_addr) = TcpBearer::accept(listener).await?;
    tracing::info!("accepted connection from {peer_addr}");

    let hs_proto = ProtocolConfig {
        id: handshake::PROTOCOL_ID,
        priority: 0,
        ingress_limit: handshake::SIZE_LIMIT,
        egress_queue_size: 4,
    };

    let mut mux = Mux::new(mux_config, RoundRobin::default(), MODE_RESPONDER);
    let (hs_send, hs_recv) = mux.register(&hs_proto);

    let mut channels = Vec::new();
    for proto in protocols {
        let (send, recv) = mux.register(proto);
        channels.push((CodecSend::new(send), CodecRecv::new(recv)));
    }

    let running = mux.run(bearer);

    let hs_result = handshake::run_server(
        CodecSend::new(hs_send),
        CodecRecv::new(hs_recv),
        |client_versions| n2n::negotiate(client_versions, magic),
    )
    .await;

    match hs_result {
        Ok((version, _params)) => {
            tracing::info!("handshake negotiated: version {version}");
        }
        Err(e) => {
            running.abort();
            return Err(e.into());
        }
    }

    Ok(Connection { running, channels })
}

/// Connect to a Cardano node in duplex mode: registers each protocol in both
/// directions (initiator and responder). Returns separate channel sets.
pub async fn connect_duplex(
    host: &str,
    magic: u64,
    initiator_protocols: &[ProtocolConfig],
    responder_protocols: &[ProtocolConfig],
    mux_config: MuxConfig,
) -> Result<DuplexConnection, Box<dyn std::error::Error + Send + Sync>> {
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

    let mut mux = Mux::new(mux_config, RoundRobin::default(), MODE_INITIATOR);
    let (hs_send, hs_recv) = mux.register(&hs_proto);

    let mut initiator_channels = Vec::new();
    for proto in initiator_protocols {
        let (send, recv) = mux.register_with_mode(proto, MODE_INITIATOR);
        initiator_channels.push((CodecSend::new(send), CodecRecv::new(recv)));
    }

    let mut responder_channels = Vec::new();
    for proto in responder_protocols {
        let (send, recv) = mux.register_with_mode(proto, MODE_RESPONDER);
        responder_channels.push((CodecSend::new(send), CodecRecv::new(recv)));
    }

    let running = mux.run(bearer);

    let versions = n2n::version_table(&n2n::VersionData {
        network_magic: magic,
        initiator_only_diffusion_mode: false,
        peer_sharing: 0,
        query: false,
    });

    let hs_result =
        handshake::run_client(CodecSend::new(hs_send), CodecRecv::new(hs_recv), versions).await;

    match hs_result {
        Ok(handshake::HandshakeResult::Accepted { version_number, .. }) => {
            tracing::info!("handshake accepted (duplex): version {version_number}");
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

    Ok(DuplexConnection {
        running,
        initiator_channels,
        responder_channels,
    })
}

/// Accept a duplex connection: registers each protocol in both directions.
pub async fn accept_duplex(
    listener: &tokio::net::TcpListener,
    magic: u64,
    initiator_protocols: &[ProtocolConfig],
    responder_protocols: &[ProtocolConfig],
    mux_config: MuxConfig,
) -> Result<DuplexConnection, Box<dyn std::error::Error + Send + Sync>> {
    let (bearer, peer_addr) = TcpBearer::accept(listener).await?;
    tracing::info!("accepted duplex connection from {peer_addr}");

    let hs_proto = ProtocolConfig {
        id: handshake::PROTOCOL_ID,
        priority: 0,
        ingress_limit: handshake::SIZE_LIMIT,
        egress_queue_size: 4,
    };

    let mut mux = Mux::new(mux_config, RoundRobin::default(), MODE_RESPONDER);
    let (hs_send, hs_recv) = mux.register(&hs_proto);

    let mut initiator_channels = Vec::new();
    for proto in initiator_protocols {
        let (send, recv) = mux.register_with_mode(proto, MODE_INITIATOR);
        initiator_channels.push((CodecSend::new(send), CodecRecv::new(recv)));
    }

    let mut responder_channels = Vec::new();
    for proto in responder_protocols {
        let (send, recv) = mux.register_with_mode(proto, MODE_RESPONDER);
        responder_channels.push((CodecSend::new(send), CodecRecv::new(recv)));
    }

    let running = mux.run(bearer);

    let hs_result = handshake::run_server(
        CodecSend::new(hs_send),
        CodecRecv::new(hs_recv),
        |client_versions| n2n::negotiate(client_versions, magic),
    )
    .await;

    match hs_result {
        Ok((version, _params)) => {
            tracing::info!("handshake negotiated (duplex): version {version}");
        }
        Err(e) => {
            running.abort();
            return Err(e.into());
        }
    }

    Ok(DuplexConnection {
        running,
        initiator_channels,
        responder_channels,
    })
}
