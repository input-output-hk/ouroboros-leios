//! Duplex peer task: runs both initiator (client) and responder (server)
//! protocols on a single connection.
//!
//! Combines the sub-tasks from `peer_task` (client-side) and
//! `responder_task` (server-side) on one mux, using `connect_duplex()`
//! or `accept_duplex()` for connection setup.

use std::sync::Arc;
use std::time::Duration;

use tokio::sync::mpsc;

use crate::mux::MuxConfig;
use crate::protocols::peersharing::PeerAddress;
use crate::types::Point;

use super::chain_store::ChainStore;
use super::connect::{self, DuplexConnection};
use super::peer_task::{
    client_protocol_configs, spawn_blockfetch, spawn_chainsync, spawn_keepalive, spawn_peersharing,
};
use super::responder_task::server_protocol_configs;
use super::server_handlers;
use super::types::{PeerCommand, PeerEvent};
use super::PeerId;

/// Configuration for a duplex peer task that connects outbound.
pub(crate) struct DuplexTaskConfig {
    pub peer_id: PeerId,
    pub address: String,
    pub network_magic: u64,
    pub keepalive_interval: Duration,
    pub sdu_timeout: Duration,
    pub chain_store: Arc<ChainStore>,
    pub peer_provider: Arc<dyn Fn(u8) -> Vec<PeerAddress> + Send + Sync>,
    pub event_sender: mpsc::Sender<(PeerId, PeerEvent)>,
    pub command_receiver: mpsc::Receiver<PeerCommand>,
}

/// Run a duplex peer task. Connects outbound, then runs both client and
/// server protocol sub-tasks on the same mux.
pub(crate) async fn run_duplex_task(mut config: DuplexTaskConfig) {
    let peer_id = config.peer_id;
    let event_sender = config.event_sender.clone();

    // Connect with duplex registration.
    let mux_config = MuxConfig {
        sdu_timeout: config.sdu_timeout,
        ..MuxConfig::default()
    };

    let conn: DuplexConnection = match connect::connect_duplex(
        &config.address,
        config.network_magic,
        &client_protocol_configs(),
        &server_protocol_configs(),
        mux_config,
    )
    .await
    {
        Ok(conn) => conn,
        Err(e) => {
            let reason = format!("connect duplex: {e}");
            let _ = event_sender
                .send((peer_id, PeerEvent::Failed { reason }))
                .await;
            return;
        }
    };

    let _ = event_sender.send((peer_id, PeerEvent::Connected)).await;

    // --- Initiator (client) sub-tasks ---
    let mut init_channels = conn.initiator_channels.into_iter();
    let (cs_send, cs_recv) = init_channels.next().expect("chainsync initiator channel");
    let (ka_send, ka_recv) = init_channels.next().expect("keepalive initiator channel");
    let (bf_send, bf_recv) = init_channels.next().expect("blockfetch initiator channel");
    let (ps_send, ps_recv) = init_channels.next().expect("peersharing initiator channel");

    let (fetch_sender, fetch_receiver) = mpsc::channel::<(Point, Point)>(16);
    let (peer_share_sender, peer_share_receiver) = mpsc::channel::<u8>(4);

    let mut cs_client = spawn_chainsync(cs_send, cs_recv, peer_id, event_sender.clone());
    let ka_client = spawn_keepalive(
        ka_send,
        ka_recv,
        peer_id,
        config.keepalive_interval,
        event_sender.clone(),
    );
    let bf_client = spawn_blockfetch(
        bf_send,
        bf_recv,
        peer_id,
        fetch_receiver,
        event_sender.clone(),
    );
    let ps_client = spawn_peersharing(
        ps_send,
        ps_recv,
        peer_id,
        peer_share_receiver,
        event_sender.clone(),
    );

    // --- Responder (server) sub-tasks ---
    let mut resp_channels = conn.responder_channels.into_iter();
    let (cs_srv_send, cs_srv_recv) = resp_channels.next().expect("chainsync responder channel");
    let (bf_srv_send, bf_srv_recv) = resp_channels.next().expect("blockfetch responder channel");
    let (ts_srv_send, ts_srv_recv) = resp_channels
        .next()
        .expect("txsubmission responder channel");
    let (ps_srv_send, ps_srv_recv) = resp_channels.next().expect("peersharing responder channel");
    let (ka_srv_send, ka_srv_recv) = resp_channels.next().expect("keepalive responder channel");

    let cs_server = tokio::spawn(server_handlers::serve_chainsync(
        cs_srv_send,
        cs_srv_recv,
        config.chain_store.clone(),
    ));
    let bf_server = tokio::spawn(server_handlers::serve_blockfetch(
        bf_srv_send,
        bf_srv_recv,
        config.chain_store.clone(),
    ));
    let ts_server = tokio::spawn(server_handlers::serve_txsubmission(
        ts_srv_send,
        ts_srv_recv,
        peer_id,
        event_sender.clone(),
    ));
    let ps_server = tokio::spawn(server_handlers::serve_peersharing(
        ps_srv_send,
        ps_srv_recv,
        config.peer_provider,
    ));
    let ka_server = tokio::spawn(server_handlers::serve_keepalive(ka_srv_send, ka_srv_recv));

    // Main select loop: dispatch commands and detect ChainSync client exit.
    loop {
        tokio::select! {
            cmd = config.command_receiver.recv() => {
                match cmd {
                    Some(PeerCommand::FetchBlocks { from, to }) => {
                        let _ = fetch_sender.send((from, to)).await;
                    }
                    Some(PeerCommand::RequestPeers { amount }) => {
                        let _ = peer_share_sender.send(amount).await;
                    }
                    Some(PeerCommand::Disconnect) | None => break,
                }
            }
            result = &mut cs_client => {
                if let Err(e) = result {
                    tracing::warn!("peer {peer_id}: chainsync client panicked: {e}");
                }
                break;
            }
        }
    }

    // Clean up all sub-tasks.
    cs_client.abort();
    ka_client.abort();
    bf_client.abort();
    ps_client.abort();
    cs_server.abort();
    bf_server.abort();
    ts_server.abort();
    ps_server.abort();
    ka_server.abort();
    conn.running.abort();
}
