//! Coordinator wrapper: translates NodeConfig into CoordinatorConfig,
//! spawns the coordinator, and issues AddPeer commands for configured peers.

use std::collections::HashMap;
use std::time::Duration;

use net_core::multi_peer::types::NetworkCommand;
use net_core::multi_peer::{spawn_coordinator, CoordinatorConfig, CoordinatorHandle};
use net_core::mux::scheduler::SchedulerType;

use crate::config::NodeConfig;

/// Parse a scheduler name string into a `SchedulerType`.
fn parse_scheduler(name: &str) -> Result<SchedulerType, Box<dyn std::error::Error + Send + Sync>> {
    match name.to_lowercase().as_str() {
        "round-robin" | "roundrobin" | "rr" => Ok(SchedulerType::RoundRobin),
        "strict-priority" | "strictpriority" | "sp" => Ok(SchedulerType::StrictPriority),
        "priority-wfq" | "prioritywfq" | "wfq" => Ok(SchedulerType::PriorityWfq),
        _ => Err(format!(
            "unknown scheduler: {name} (expected round-robin, strict-priority, or priority-wfq)"
        )
        .into()),
    }
}

/// Start the multi-peer coordinator and add configured peers.
pub async fn start(
    config: &NodeConfig,
) -> Result<CoordinatorHandle, Box<dyn std::error::Error + Send + Sync>> {
    let coordinator_config = CoordinatorConfig {
        network_magic: config.network_magic,
        max_peers: config.max_peers,
        keepalive_interval: Duration::from_secs(config.keepalive_interval_secs),
        sdu_timeout: Duration::from_secs(900),
        listen_address: config.listen_address.clone(),
        chain_store_capacity: config.chain_store_capacity,
        duplex: true,
        leios_enabled: config.leios_enabled,
        leios_dedup_window: config.leios_dedup_window,
        traffic_class_overrides: HashMap::new(),
        scheduler_type: parse_scheduler(&config.scheduler)?,
        max_handshaking: config.max_handshaking,
        max_connections_per_ip: config.max_connections_per_ip,
    };

    let handle = spawn_coordinator(coordinator_config);

    // Add configured outbound peers.
    for peer in &config.peers {
        let _ = handle
            .commands
            .send(NetworkCommand::AddPeer {
                address: peer.address.clone(),
            })
            .await;
    }

    Ok(handle)
}
