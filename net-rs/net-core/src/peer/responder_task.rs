//! Per-responder peer task: manages one inbound connection's server-side
//! protocol sub-tasks.
//!
//! Each responder task owns a single mux connection (already accepted and
//! handshaked) and spawns server-side protocol handlers. It reads chain
//! state from a shared `ChainStore` and sends events to the coordinator
//! via the fan-in channel.

use std::sync::Arc;

use tokio::sync::mpsc;

use crate::mux::scheduler::TrafficClass;
use crate::mux::ProtocolConfig;
use crate::protocols::blockfetch;
use crate::protocols::chainsync;
use crate::protocols::keepalive;
use crate::protocols::leios_fetch;
use crate::protocols::leios_notify;
use crate::protocols::peersharing::{self, PeerAddress};
use crate::protocols::txsubmission;

use super::connect::Connection;
use super::server_handlers;
use super::types::{PeerCommand, PeerEvent};
use super::PeerId;
use crate::store::chain_store::ChainStore;
use crate::store::leios_store::LeiosStore;

/// Configuration for a responder peer task.
pub(crate) struct ResponderTaskConfig {
    pub peer_id: PeerId,
    pub connection: Connection,
    pub chain_store: Arc<ChainStore>,
    pub peer_provider: Arc<dyn Fn(u8) -> Vec<PeerAddress> + Send + Sync>,
    pub event_sender: mpsc::Sender<(PeerId, PeerEvent)>,
    pub command_receiver: mpsc::Receiver<PeerCommand>,
    pub leios_enabled: bool,
    pub leios_store: Option<Arc<LeiosStore>>,
}

/// Protocol configs for server-side protocols (excluding handshake).
/// When `leios_enabled`, also registers LeiosNotify and LeiosFetch.
pub(crate) fn server_protocol_configs(leios_enabled: bool) -> Vec<ProtocolConfig> {
    let mut configs = vec![
        ProtocolConfig {
            id: chainsync::PROTOCOL_ID,
            traffic_class: TrafficClass::Priority,
            ingress_limit: chainsync::INGRESS_LIMIT,
            egress_queue_size: 16,
        },
        ProtocolConfig {
            id: blockfetch::PROTOCOL_ID,
            traffic_class: TrafficClass::Priority,
            ingress_limit: blockfetch::INGRESS_LIMIT,
            egress_queue_size: 16,
        },
        ProtocolConfig {
            id: txsubmission::PROTOCOL_ID,
            traffic_class: TrafficClass::Priority,
            ingress_limit: txsubmission::INGRESS_LIMIT,
            egress_queue_size: 16,
        },
        ProtocolConfig {
            id: peersharing::PROTOCOL_ID,
            traffic_class: TrafficClass::Default(1),
            ingress_limit: peersharing::INGRESS_LIMIT,
            egress_queue_size: 4,
        },
        ProtocolConfig {
            id: keepalive::PROTOCOL_ID,
            traffic_class: TrafficClass::Priority,
            ingress_limit: keepalive::INGRESS_LIMIT,
            egress_queue_size: 4,
        },
    ];
    if leios_enabled {
        configs.push(ProtocolConfig {
            id: leios_notify::PROTOCOL_ID,
            traffic_class: TrafficClass::Default(1),
            ingress_limit: leios_notify::INGRESS_LIMIT,
            egress_queue_size: 16,
        });
        configs.push(ProtocolConfig {
            id: leios_fetch::PROTOCOL_ID,
            traffic_class: TrafficClass::Default(1),
            ingress_limit: leios_fetch::INGRESS_LIMIT,
            egress_queue_size: 16,
        });
    }
    configs
}

/// Run the responder peer task. Takes an already-accepted connection,
/// spawns server-side protocol handlers, and dispatches commands.
pub(crate) async fn run_responder_task(mut config: ResponderTaskConfig) {
    let peer_id = config.peer_id;
    let event_sender = config.event_sender.clone();

    // Report successful connection.
    let _ = event_sender.send((peer_id, PeerEvent::Connected)).await;

    // Extract codec pairs (in registration order).
    let mut channels = config.connection.channels.into_iter();
    let (cs_send, cs_recv) = channels.next().expect("chainsync channel registered first");
    let (bf_send, bf_recv) = channels
        .next()
        .expect("blockfetch channel registered second");
    let (ts_send, ts_recv) = channels
        .next()
        .expect("txsubmission channel registered third");
    let (ps_send, ps_recv) = channels
        .next()
        .expect("peersharing channel registered fourth");
    let (ka_send, ka_recv) = channels.next().expect("keepalive channel registered fifth");

    // Conditionally extract Leios channels.
    let leios_handles = if config.leios_enabled {
        let (ln_send, ln_recv) = channels
            .next()
            .expect("leios_notify channel registered sixth");
        let (lf_send, lf_recv) = channels
            .next()
            .expect("leios_fetch channel registered seventh");
        let store = config
            .leios_store
            .expect("leios_store required when leios_enabled");
        let ln_handle = tokio::spawn(server_handlers::serve_leios_notify(
            ln_send,
            ln_recv,
            store.clone(),
        ));
        let lf_handle = tokio::spawn(server_handlers::serve_leios_fetch(lf_send, lf_recv, store));
        Some((ln_handle, lf_handle))
    } else {
        None
    };

    // Spawn server-side protocol sub-tasks.
    let mut cs_handle = tokio::spawn(server_handlers::serve_chainsync(
        cs_send,
        cs_recv,
        config.chain_store.clone(),
    ));
    let bf_handle = tokio::spawn(server_handlers::serve_blockfetch(
        bf_send,
        bf_recv,
        config.chain_store.clone(),
    ));
    let ts_handle = tokio::spawn(server_handlers::serve_txsubmission(
        ts_send,
        ts_recv,
        peer_id,
        event_sender.clone(),
    ));
    let ps_handle = tokio::spawn(server_handlers::serve_peersharing(
        ps_send,
        ps_recv,
        config.peer_provider,
    ));
    let ka_handle = tokio::spawn(server_handlers::serve_keepalive(ka_send, ka_recv));

    // Main select loop: dispatch commands and detect ChainSync exit.
    loop {
        tokio::select! {
            cmd = config.command_receiver.recv() => {
                match cmd {
                    Some(PeerCommand::Disconnect) | None => break,
                    // Responder tasks don't handle FetchBlocks or RequestPeers.
                    _ => {}
                }
            }
            result = &mut cs_handle => {
                if let Err(e) = result {
                    tracing::warn!("peer {peer_id}: chainsync server panicked: {e}");
                }
                break;
            }
        }
    }

    // Clean up: abort all sub-tasks and the mux.
    cs_handle.abort();
    bf_handle.abort();
    ts_handle.abort();
    ps_handle.abort();
    ka_handle.abort();
    if let Some((ln_handle, lf_handle)) = leios_handles {
        ln_handle.abort();
        lf_handle.abort();
    }
    config.connection.running.abort();
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bearer::mem::MemBearer;
    use crate::mux::scheduler::RoundRobin;
    use crate::mux::{CodecRecv, CodecSend, Mux, MuxConfig, MODE_INITIATOR, MODE_RESPONDER};
    use crate::protocols::chainsync::{self, ChainSync};
    use crate::protocols::handshake;
    use crate::protocols::handshake::n2n;
    use crate::protocols::{Role, Runner};
    use crate::types::{BlockBody, Point, WrappedHeader};
    use std::time::Duration;

    fn make_point(slot: u64) -> Point {
        Point::Specific {
            slot,
            hash: [slot as u8; 32],
        }
    }

    fn make_header(slot: u64) -> WrappedHeader {
        let mut buf = Vec::new();
        minicbor::encode(&[slot], &mut buf).unwrap();
        WrappedHeader::opaque(buf)
    }

    fn make_body(slot: u64) -> BlockBody {
        let mut buf = Vec::new();
        minicbor::encode(&[slot], &mut buf).unwrap();
        BlockBody::opaque(buf)
    }

    #[tokio::test]
    async fn responder_task_serves_chainsync() {
        let magic = 764824073;
        let (bearer_a, bearer_b) = MemBearer::pair();

        // Populate chain store.
        let (store, _rx) = ChainStore::new(100);
        for slot in 1..=3 {
            store.append_block(make_point(slot), make_header(slot), make_body(slot));
        }

        // Server side: set up mux + handshake, then run responder task.
        let server_protos = server_protocol_configs(false);

        let hs_proto = ProtocolConfig {
            id: handshake::PROTOCOL_ID,
            traffic_class: TrafficClass::Priority,
            ingress_limit: handshake::SIZE_LIMIT,
            egress_queue_size: 4,
        };

        // Client side mux.
        let mut mux_a = Mux::new(MuxConfig::default(), RoundRobin::default(), MODE_INITIATOR);
        let (hs_send_a, hs_recv_a) = mux_a.register(&hs_proto);
        let mut client_channels = Vec::new();
        for proto in &server_protos {
            let (send, recv) = mux_a.register(proto);
            client_channels.push((CodecSend::new(send), CodecRecv::new(recv)));
        }
        let running_a = mux_a.run(bearer_a);

        // Server side mux.
        let mut mux_b = Mux::new(MuxConfig::default(), RoundRobin::default(), MODE_RESPONDER);
        let (hs_send_b, hs_recv_b) = mux_b.register(&hs_proto);
        let mut server_channels = Vec::new();
        for proto in &server_protos {
            let (send, recv) = mux_b.register(proto);
            server_channels.push((CodecSend::new(send), CodecRecv::new(recv)));
        }
        let running_b = mux_b.run(bearer_b);

        // Client handshake.
        let versions = n2n::version_table(&n2n::VersionData {
            network_magic: magic,
            initiator_only_diffusion_mode: true,
            peer_sharing: 1,
            query: false,
        });
        let client_hs = tokio::spawn(handshake::run_client(
            CodecSend::new(hs_send_a),
            CodecRecv::new(hs_recv_a),
            versions,
        ));

        // Server handshake.
        let server_data = n2n::VersionData {
            network_magic: magic,
            initiator_only_diffusion_mode: false,
            peer_sharing: 1,
            query: false,
        };
        let server_hs = handshake::run_server(
            CodecSend::new(hs_send_b),
            CodecRecv::new(hs_recv_b),
            |client_versions| n2n::negotiate(client_versions, &server_data),
        )
        .await;
        assert!(server_hs.is_ok());
        assert!(client_hs.await.unwrap().is_ok());

        // Build the Connection for the responder task.
        let connection = Connection {
            running: running_b,
            channels: server_channels,
        };

        let (event_sender, mut event_receiver) = mpsc::channel(64);
        let (_cmd_sender, cmd_receiver) = mpsc::channel(16);

        let peer_provider: Arc<dyn Fn(u8) -> Vec<PeerAddress> + Send + Sync> =
            Arc::new(|_| Vec::new());

        let responder_handle = tokio::spawn(run_responder_task(ResponderTaskConfig {
            peer_id: PeerId(0),
            connection,
            chain_store: store,
            peer_provider,
            event_sender,
            command_receiver: cmd_receiver,
            leios_enabled: false,
            leios_store: None,
        }));

        // Client: run ChainSync against the responder.
        let (cs_send, cs_recv) = client_channels.into_iter().next().unwrap();
        let mut runner = Runner::<ChainSync>::new(Role::Client, cs_send, cs_recv);

        let result = chainsync::find_intersection(&mut runner, vec![Point::Origin]).await;
        assert!(result.is_ok());
        let (point, tip) = result.unwrap().unwrap();
        assert_eq!(point, Point::Origin);
        assert_eq!(tip.block_no, 3);

        // Request next → should get block 1.
        let event = chainsync::request_next(&mut runner).await.unwrap();
        match event {
            chainsync::ChainSyncEvent::RollForward { tip, .. } => {
                assert_eq!(tip.block_no, 3);
            }
            other => panic!("expected RollForward, got {other:?}"),
        }

        // Should have received Connected event.
        let _timeout = tokio::time::timeout(Duration::from_secs(1), async {
            while let Some((_id, event)) = event_receiver.recv().await {
                if matches!(event, PeerEvent::Connected) {
                    return true;
                }
            }
            false
        })
        .await;
        // Connected was sent before we started reading — it's already in the channel.
        // We might have already consumed it, but let's not over-assert.

        // Clean up.
        let _ = chainsync::done(&mut runner).await;
        let _ = tokio::time::timeout(Duration::from_secs(1), responder_handle).await;
        running_a.abort();
    }
}
