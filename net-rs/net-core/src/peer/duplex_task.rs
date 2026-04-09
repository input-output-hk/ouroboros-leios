//! Duplex peer task: runs both initiator (client) and responder (server)
//! protocols on a single connection.
//!
//! Reuses the client sub-tasks from `peer_task` alongside the server
//! handlers from `server_handlers` on one mux, using `connect_duplex()`
//! or `accept_duplex()` for connection setup.

use std::sync::Arc;
use std::time::Duration;

use tokio::sync::mpsc;

use crate::mux::scheduler::TrafficClass;
use crate::mux::MuxConfig;
use crate::protocols::peersharing::PeerAddress;
use crate::protocols::txsubmission::PendingTx;
use crate::types::Point;

use super::command_dispatch::{dispatch_command, ClientProtocolSenders};
use super::connect::{self, DuplexConnection};
use super::peer_task::server_protocol_configs;
use super::peer_task::{
    client_protocol_configs, spawn_blockfetch, spawn_chainsync, spawn_keepalive, spawn_leios_fetch,
    spawn_leios_notify, spawn_peersharing, spawn_txsubmission, LeiosFetchCommand,
};
use super::server_handlers;
use super::types::{PeerCommand, PeerEvent};
use super::PeerId;
use crate::store::chain_store::ChainStore;
use crate::store::leios_store::LeiosStore;

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
    pub leios_enabled: bool,
    pub leios_store: Option<Arc<LeiosStore>>,
    pub traffic_class_overrides: std::collections::HashMap<u16, TrafficClass>,
    pub scheduler_type: crate::mux::scheduler::SchedulerType,
}

/// Configuration for a duplex peer task from an already-accepted connection.
pub(crate) struct AcceptedDuplexTaskConfig {
    pub peer_id: PeerId,
    pub connection: DuplexConnection,
    pub keepalive_interval: Duration,
    pub chain_store: Arc<ChainStore>,
    pub peer_provider: Arc<dyn Fn(u8) -> Vec<PeerAddress> + Send + Sync>,
    pub event_sender: mpsc::Sender<(PeerId, PeerEvent)>,
    pub command_receiver: mpsc::Receiver<PeerCommand>,
    pub leios_enabled: bool,
    pub leios_store: Option<Arc<LeiosStore>>,
}

/// Run a duplex peer task. Connects outbound, then runs both client and
/// server protocol sub-tasks on the same mux.
pub(crate) async fn run_duplex_task(config: DuplexTaskConfig) {
    let peer_id = config.peer_id;
    let event_sender = config.event_sender.clone();

    // Connect with duplex registration.
    let mux_config = MuxConfig {
        sdu_timeout: config.sdu_timeout,
        ..MuxConfig::default()
    };

    let mut client_protos = client_protocol_configs(config.leios_enabled);
    let mut server_protos = server_protocol_configs(config.leios_enabled);
    for p in client_protos.iter_mut().chain(server_protos.iter_mut()) {
        if let Some(tc) = config.traffic_class_overrides.get(&p.id) {
            p.traffic_class = *tc;
        }
    }

    let conn: DuplexConnection = match connect::connect_duplex(
        &config.address,
        config.network_magic,
        &client_protos,
        &server_protos,
        mux_config,
        config.scheduler_type,
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

    let _ = event_sender
        .send((
            peer_id,
            PeerEvent::Connected {
                mux_stats: conn.running.stats.clone(),
            },
        ))
        .await;

    run_duplex_protocols(
        conn,
        DuplexProtocolParams {
            peer_id: config.peer_id,
            keepalive_interval: config.keepalive_interval,
            leios_enabled: config.leios_enabled,
            chain_store: config.chain_store,
            peer_provider: config.peer_provider,
            leios_store: config.leios_store,
            event_sender: config.event_sender,
            command_receiver: config.command_receiver,
        },
    )
    .await;
}

/// Run a duplex peer task from an already-accepted connection.
pub(crate) async fn run_accepted_duplex_task(config: AcceptedDuplexTaskConfig) {
    let peer_id = config.peer_id;
    let event_sender = config.event_sender.clone();
    let conn = config.connection;

    let _ = event_sender
        .send((
            peer_id,
            PeerEvent::Connected {
                mux_stats: conn.running.stats.clone(),
            },
        ))
        .await;

    run_duplex_protocols(
        conn,
        DuplexProtocolParams {
            peer_id: config.peer_id,
            keepalive_interval: config.keepalive_interval,
            leios_enabled: config.leios_enabled,
            chain_store: config.chain_store,
            peer_provider: config.peer_provider,
            leios_store: config.leios_store,
            event_sender: config.event_sender,
            command_receiver: config.command_receiver,
        },
    )
    .await;
}

/// Shared parameters for duplex protocol wiring.
struct DuplexProtocolParams {
    peer_id: PeerId,
    keepalive_interval: Duration,
    leios_enabled: bool,
    chain_store: Arc<ChainStore>,
    peer_provider: Arc<dyn Fn(u8) -> Vec<PeerAddress> + Send + Sync>,
    leios_store: Option<Arc<LeiosStore>>,
    event_sender: mpsc::Sender<(PeerId, PeerEvent)>,
    command_receiver: mpsc::Receiver<PeerCommand>,
}

/// Shared protocol wiring for duplex connections (both outbound and accepted).
async fn run_duplex_protocols(conn: DuplexConnection, params: DuplexProtocolParams) {
    let DuplexProtocolParams {
        peer_id,
        keepalive_interval,
        leios_enabled,
        chain_store,
        peer_provider,
        leios_store,
        event_sender,
        mut command_receiver,
    } = params;
    // --- Initiator (client) sub-tasks ---
    let mut init_channels = conn.initiator_channels.into_iter();
    let (cs_send, cs_recv) = init_channels.next().expect("chainsync initiator channel");
    let (ka_send, ka_recv) = init_channels.next().expect("keepalive initiator channel");
    let (bf_send, bf_recv) = init_channels.next().expect("blockfetch initiator channel");
    let (ps_send, ps_recv) = init_channels.next().expect("peersharing initiator channel");
    let (ts_send, ts_recv) = init_channels
        .next()
        .expect("txsubmission initiator channel");

    let (fetch_sender, fetch_receiver) = mpsc::channel::<(Point, Point)>(16);
    let (peer_share_sender, peer_share_receiver) = mpsc::channel::<u8>(4);
    let (tx_submit_sender, tx_submit_receiver) = mpsc::channel::<PendingTx>(16);
    let (cs_reintersect_sender, cs_reintersect_receiver) = mpsc::channel::<()>(4);

    let mut cs_client = spawn_chainsync(
        cs_send,
        cs_recv,
        peer_id,
        chain_store.clone(),
        event_sender.clone(),
        cs_reintersect_receiver,
    );
    let ka_client = spawn_keepalive(
        ka_send,
        ka_recv,
        peer_id,
        keepalive_interval,
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
    let ts_client = spawn_txsubmission(
        ts_send,
        ts_recv,
        peer_id,
        tx_submit_receiver,
        event_sender.clone(),
    );

    // Conditionally spawn Leios client sub-tasks.
    let leios_client_handles = if leios_enabled {
        let (ln_send, ln_recv) = init_channels
            .next()
            .expect("leios_notify initiator channel");
        let (lf_send, lf_recv) = init_channels.next().expect("leios_fetch initiator channel");
        let (lf_cmd_sender, lf_cmd_receiver) = mpsc::channel::<LeiosFetchCommand>(16);
        let ln_handle = spawn_leios_notify(ln_send, ln_recv, peer_id, event_sender.clone());
        let lf_handle = spawn_leios_fetch(
            lf_send,
            lf_recv,
            peer_id,
            lf_cmd_receiver,
            event_sender.clone(),
        );
        Some((ln_handle, lf_handle, lf_cmd_sender))
    } else {
        None
    };

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
        chain_store.clone(),
    ));
    let bf_server = tokio::spawn(server_handlers::serve_blockfetch(
        bf_srv_send,
        bf_srv_recv,
        chain_store.clone(),
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
        peer_provider,
    ));
    let ka_server = tokio::spawn(server_handlers::serve_keepalive(ka_srv_send, ka_srv_recv));

    // Conditionally spawn Leios server sub-tasks.
    let leios_server_handles = if leios_enabled {
        let (ln_srv_send, ln_srv_recv) = resp_channels
            .next()
            .expect("leios_notify responder channel");
        let (lf_srv_send, lf_srv_recv) =
            resp_channels.next().expect("leios_fetch responder channel");
        let store = leios_store.expect("leios_store required when leios_enabled");
        let ln_server = tokio::spawn(server_handlers::serve_leios_notify(
            ln_srv_send,
            ln_srv_recv,
            store.clone(),
        ));
        let lf_server = tokio::spawn(server_handlers::serve_leios_fetch(
            lf_srv_send,
            lf_srv_recv,
            store,
        ));
        Some((ln_server, lf_server))
    } else {
        None
    };

    // Build shared command senders for dispatch.
    let senders = ClientProtocolSenders {
        fetch: fetch_sender,
        peer_share: peer_share_sender,
        tx_submit: tx_submit_sender,
        leios_fetch: leios_client_handles.as_ref().map(|(_, _, lf)| lf.clone()),
        chainsync_reintersect: cs_reintersect_sender,
    };

    // Main select loop: dispatch commands and detect ChainSync client exit.
    loop {
        tokio::select! {
            cmd = command_receiver.recv() => {
                if !dispatch_command(cmd, &senders).await {
                    break;
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
    ts_client.abort();
    if let Some((ln_handle, lf_handle, _)) = leios_client_handles {
        ln_handle.abort();
        lf_handle.abort();
    }
    cs_server.abort();
    bf_server.abort();
    ts_server.abort();
    ps_server.abort();
    ka_server.abort();
    if let Some((ln_handle, lf_handle)) = leios_server_handles {
        ln_handle.abort();
        lf_handle.abort();
    }
    conn.running.abort();
}
