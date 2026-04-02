//! net-cluster: orchestrate a local cluster of net-node instances.
//!
//! Generates random network topology, spawns net-node child processes with
//! layered configs, and aggregates their telemetry into a time-ordered JSONL
//! event log.

mod aggregator;
mod config;
mod overlay;
mod process;
mod server;
mod topology;
mod types;

use std::path::{Path, PathBuf};
use std::sync::Arc;

use clap::Parser;
use tokio::sync::RwLock;

#[derive(Parser)]
#[command(
    name = "net-cluster",
    about = "Orchestrate a local cluster of net-node instances"
)]
struct Cli {
    /// Cluster config file (TOML).
    #[arg(long = "config", value_name = "FILE", default_value = "cluster.toml")]
    config: String,

    /// Override individual config values (repeatable, key=value).
    #[arg(long = "set", value_name = "KEY=VALUE")]
    set: Vec<String>,

    /// Path to the net-node binary.
    #[arg(long = "net-node-bin")]
    net_node_bin: Option<String>,

    /// Override individual net-node config values (repeatable, key=value).
    /// These are forwarded as --set to each spawned net-node process.
    #[arg(long = "node-set", value_name = "KEY=VALUE")]
    node_set: Vec<String>,

    /// Forward child stdout/stderr to this process's stdout.
    #[arg(long = "verbose", short = 'v')]
    verbose: bool,
}

/// A running set of child node processes with their temp overlay directory.
struct RunningCluster {
    pm: process::ProcessManager,
    temp_dir: PathBuf,
}

/// Spawn child node processes for the given topology.
fn spawn_cluster(
    config: &config::ClusterConfig,
    net_node_bin: &Path,
    topo: &topology::Topology,
    node_overrides: &[String],
    node_config: &std::collections::HashMap<String, serde_json::Value>,
) -> Result<RunningCluster, Box<dyn std::error::Error + Send + Sync>> {
    let temp_dir = std::env::temp_dir().join(format!(
        "net-cluster-{}-{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap_or_default()
            .as_millis()
    ));
    let overlays = overlay::generate_overlays(
        topo,
        &temp_dir,
        config.aggregator_port,
        config.stats_interval_secs,
        node_config,
    )?;

    let log_dir = PathBuf::from("logs");
    let mut pm = process::ProcessManager::new(
        net_node_bin.to_path_buf(),
        config.base_config.clone(),
        log_dir,
        node_overrides.to_vec(),
    );

    let extra_config = overlays.node_config_path.as_deref();
    for (i, node) in topo.nodes.iter().enumerate() {
        pm.spawn(i, &node.node_id, &overlays.paths[i], extra_config)?;
    }

    Ok(RunningCluster { pm, temp_dir })
}

/// Shut down child processes and clean up temp overlay files.
async fn shutdown_cluster(cluster: &mut RunningCluster) {
    cluster.pm.shutdown(std::time::Duration::from_secs(5)).await;
    overlay::cleanup(&cluster.temp_dir);
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
    tracing_subscriber::fmt::init();

    let cli = Cli::parse();

    // Step 1: Load cluster config.
    let mut current_config = config::load(&cli.config, &cli.set)?;
    tracing::info!(
        "loaded cluster config: {} nodes, degree={}, latency={}–{}ms, ports {}–{}",
        current_config.num_nodes,
        current_config.degree,
        current_config.min_latency_ms,
        current_config.max_latency_ms,
        current_config.base_port,
        current_config.base_port + current_config.num_nodes as u16 - 1,
    );

    // Step 2: Read total_stake from the base config.
    let total_stake = read_total_stake(&current_config.base_config)?;

    // Step 3: Generate initial topology.
    let topo = topology::generate(&current_config, total_stake);
    log_topology(&topo);

    // Step 4: Create shared event window, restart channel, and start HTTP server.
    let event_window = Arc::new(RwLock::new(types::EventWindow::new(
        current_config.event_window_size,
    )));
    let (event_tx, event_rx) = tokio::sync::mpsc::channel(4096);
    let (restart_tx, mut restart_rx) =
        tokio::sync::mpsc::channel::<config::ClusterControlConfig>(1);
    let (server_state, _server_handle) = server::start(
        current_config.aggregator_port,
        event_tx,
        topo.clone(),
        event_window.clone(),
        restart_tx,
        current_config.control_fields(),
    )
    .await?;

    // Step 5: Spawn the aggregator task (persists across restarts).
    let output_path = PathBuf::from(&current_config.output_events);
    let num_nodes = current_config.num_nodes;
    let ordering_window = current_config.ordering_window_secs;
    let agg_window = event_window.clone();
    let aggregator_handle = tokio::spawn(async move {
        if let Err(e) = aggregator::run(
            event_rx,
            &output_path,
            num_nodes,
            ordering_window,
            agg_window,
        )
        .await
        {
            tracing::error!("aggregator error: {e}");
        }
    });

    // Step 6: Resolve net-node binary.
    let net_node_bin = process::resolve_net_node_bin(cli.net_node_bin.as_deref())?;
    tracing::info!("using net-node binary: {}", net_node_bin.display());

    // Track node-level config overrides across restarts.
    let initial_control = current_config.control_fields();
    let mut node_config = initial_control.node_config.clone();

    // Main restart loop: spawn cluster, wait for Ctrl-C or restart command.
    let mut cluster = spawn_cluster(
        &current_config,
        &net_node_bin,
        &topo,
        &cli.node_set,
        &node_config,
    )?;
    tracing::info!(
        "cluster running: {} nodes started, telemetry on port {}, output to {}",
        cluster.pm.count(),
        current_config.aggregator_port,
        current_config.output_events,
    );

    loop {
        tokio::select! {
            _ = tokio::signal::ctrl_c() => {
                tracing::info!("received Ctrl-C, shutting down...");
                shutdown_cluster(&mut cluster).await;
                break;
            }
            Some(overrides) = restart_rx.recv() => {
                tracing::info!("restart requested: {:?}", overrides);
                shutdown_cluster(&mut cluster).await;

                // Update node-level config from the request.
                node_config = overrides.node_config.clone();

                match current_config.with_overrides(&overrides) {
                    Ok(new_config) => {
                        current_config = new_config;
                    }
                    Err(e) => {
                        tracing::error!("invalid config overrides: {e}, re-spawning with old config");
                    }
                }

                // Generate new topology and update server state.
                let new_total_stake = read_total_stake(&current_config.base_config)?;
                let new_topo = topology::generate(&current_config, new_total_stake);
                log_topology(&new_topo);

                // Build control config with current node_config for the UI.
                let mut control = current_config.control_fields();
                control.node_config = node_config.clone();

                *server_state.topology.write().await = new_topo.clone();
                *server_state.current_config.write().await = control;
                server_state.latest_stats.write().await.clear();
                server_state.event_window.write().await.clear();
                *server_state.restarting.write().await = false;

                cluster = spawn_cluster(&current_config, &net_node_bin, &new_topo, &cli.node_set, &node_config)?;
                tracing::info!(
                    "cluster restarted: {} nodes, telemetry on port {}",
                    cluster.pm.count(),
                    current_config.aggregator_port,
                );
            }
        }
    }

    // Final shutdown.
    drop(server_state);
    drop(_server_handle);
    let _ = tokio::time::timeout(std::time::Duration::from_secs(5), aggregator_handle).await;
    tracing::info!("cluster shut down");
    Ok(())
}

fn log_topology(topo: &topology::Topology) {
    tracing::info!(
        "generated topology: {} nodes, {} edges",
        topo.nodes.len(),
        topo.edges.len()
    );
    for node in &topo.nodes {
        tracing::info!(
            "  {} @ {} (stake={}, {} peers)",
            node.node_id,
            node.listen_address,
            node.stake,
            node.peers.len()
        );
    }
}

/// Read `production.total_stake` from the base config file.
fn read_total_stake(base_config: &str) -> Result<u64, Box<dyn std::error::Error + Send + Sync>> {
    let path = Path::new(base_config);
    if !path.exists() {
        return Err(format!("base config not found: {base_config}").into());
    }
    let content = std::fs::read_to_string(path)?;
    let table: toml::Value = toml::from_str(&content)?;
    let total_stake = table
        .get("production")
        .and_then(|p| p.get("total_stake"))
        .and_then(|v| v.as_integer())
        .unwrap_or(1000) as u64;
    Ok(total_stake)
}
