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

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
    tracing_subscriber::fmt::init();

    let cli = Cli::parse();

    // Step 1: Load cluster config.
    let config = config::load(&cli.config, &cli.set)?;
    tracing::info!(
        "loaded cluster config: {} nodes, degree={}, latency={}–{}ms, ports {}–{}",
        config.num_nodes,
        config.degree,
        config.min_latency_ms,
        config.max_latency_ms,
        config.base_port,
        config.base_port + config.num_nodes as u16 - 1,
    );

    // Step 2: Read total_stake from the base config.
    let total_stake = read_total_stake(&config.base_config)?;

    // Step 3: Generate topology.
    let topo = topology::generate(&config, total_stake);
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

    // Step 4: Create shared event window and start the HTTP server.
    let event_window = Arc::new(RwLock::new(types::EventWindow::new(
        config.event_window_size,
    )));
    let (event_tx, event_rx) = tokio::sync::mpsc::channel(4096);
    let (_server_state, _server_handle) = server::start(
        config.aggregator_port,
        event_tx,
        topo.clone(),
        event_window.clone(),
    )
    .await?;

    // Step 5: Spawn the aggregator task.
    let output_path = PathBuf::from(&config.output_events);
    let num_nodes = config.num_nodes;
    let ordering_window = config.ordering_window_secs;
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

    // Step 6: Generate overlay files and spawn child processes.
    let temp_dir = std::env::temp_dir().join(format!("net-cluster-{}", std::process::id()));
    let overlays = overlay::generate_overlays(
        &topo,
        &temp_dir,
        config.aggregator_port,
        config.stats_interval_secs,
    )?;

    let net_node_bin = process::resolve_net_node_bin(cli.net_node_bin.as_deref())?;
    tracing::info!("using net-node binary: {}", net_node_bin.display());

    let log_dir = PathBuf::from("logs");
    let mut pm = process::ProcessManager::new(
        net_node_bin,
        config.base_config.clone(),
        log_dir,
        cli.node_set,
    );

    for (i, node) in topo.nodes.iter().enumerate() {
        pm.spawn(i, &node.node_id, &overlays.paths[i])?;
    }

    tracing::info!(
        "cluster running: {} nodes started, telemetry on port {}, output to {}",
        pm.count(),
        config.aggregator_port,
        config.output_events
    );

    // Step 7: Wait for shutdown signal.
    tokio::signal::ctrl_c().await?;
    tracing::info!("received Ctrl-C, shutting down...");

    // Step 8: Shutdown.
    pm.shutdown(std::time::Duration::from_secs(5)).await;

    // Drop the event sender to signal the aggregator to do a final flush.
    drop(_server_state);
    drop(_server_handle);

    // Wait for the aggregator to finish.
    let _ = tokio::time::timeout(std::time::Duration::from_secs(5), aggregator_handle).await;

    // Clean up temp files.
    overlay::cleanup(&temp_dir);

    tracing::info!("cluster shut down");
    Ok(())
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
