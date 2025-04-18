use std::{fs, path::PathBuf, process};

use anyhow::Result;
use clap::Parser;
use events::EventMonitor;
use figment::{
    providers::{Format as _, Yaml},
    Figment,
};
use sim_core::{
    clock::ClockCoordinator,
    config::{NodeId, RawParameters, RawTopology, SimConfiguration, Topology},
    events::EventTracker,
    sim::Simulation,
};
use tokio::{
    pin, select,
    sync::{mpsc, oneshot},
};
use tokio_util::sync::CancellationToken;
use tracing::{level_filters::LevelFilter, warn};
use tracing_subscriber::{layer::SubscriberExt as _, util::SubscriberInitExt, EnvFilter};

mod events;

const DEFAULT_TOPOLOGY_PATHS: &[&str] = &[
    // Docker/production path
    "/usr/local/share/leios/topology.default.yaml",
    // Development paths
    "../../data/simulation/topo-default-100.yaml",
    "../data/simulation/topo-default-100.yaml",
];

#[derive(Parser)]
struct Args {
    #[clap(default_value = None)]
    topology: Option<PathBuf>,
    output: Option<PathBuf>,
    #[clap(short, long)]
    parameters: Vec<PathBuf>,
    #[clap(short, long)]
    timescale: Option<f64>,
    #[clap(long)]
    trace_node: Vec<usize>,
    #[clap(short, long)]
    slots: Option<u64>,
    #[clap(short, long)]
    conformance_events: bool,
    #[clap(short, long)]
    aggregate_events: bool,
}

fn get_default_topology() -> Result<String> {
    let mut last_error = None;

    // Try each possible topology location
    for path in DEFAULT_TOPOLOGY_PATHS {
        match fs::read_to_string(path) {
            Ok(content) => return Ok(content),
            Err(e) => last_error = Some((path, e)),
        }
    }

    // If we get here, none of the paths worked
    let (path, error) = last_error.unwrap();
    Err(anyhow::anyhow!(
        "Could not find default topology file in any location. Last attempt '{}' failed: {}",
        path,
        error
    ))
}

fn read_config(args: &Args) -> Result<SimConfiguration> {
    let topology_str = match &args.topology {
        Some(path) => fs::read_to_string(path)?,
        None => get_default_topology()?,
    };
    let topology: Topology = {
        let raw_topology: RawTopology = serde_yaml::from_str(&topology_str)?;
        raw_topology.into()
    };
    topology.validate()?;

    let mut raw_params = Figment::new().merge(Yaml::string(include_str!(
        "../../parameters/config.default.yaml"
    )));

    for params_file in &args.parameters {
        raw_params = raw_params.merge(Yaml::file_exact(params_file));
    }

    let params: RawParameters = raw_params.extract()?;
    let mut config = SimConfiguration::build(params, topology);
    if let Some(slots) = args.slots {
        config.slots = Some(slots);
    }
    if args.conformance_events {
        config.emit_conformance_events = true;
    }
    if args.aggregate_events {
        config.aggregate_events = true;
    }
    for id in &args.trace_node {
        config.trace_nodes.insert(NodeId::new(*id));
    }
    Ok(config)
}

#[tokio::main]
async fn main() -> Result<()> {
    let fmt_layer = tracing_subscriber::fmt::layer().compact().without_time();
    let filter = EnvFilter::builder()
        .with_default_directive(LevelFilter::INFO.into())
        .from_env_lossy();
    tracing_subscriber::registry()
        .with(fmt_layer)
        .with(filter)
        .init();

    let token = CancellationToken::new();

    // Handle ctrl+c (SIGINT) at an application level, so we can report on necessary stats before shutting down.
    let (ctrlc_sink, ctrlc_source) = oneshot::channel();
    let mut ctrlc_sink = Some(ctrlc_sink);
    let ctrlc_token = token.clone();
    ctrlc::set_handler(move || {
        ctrlc_token.cancel();
        if let Some(sink) = ctrlc_sink.take() {
            let _ = sink.send(());
        } else {
            warn!("force quitting");
            process::exit(0);
        }
    })?;

    let args = Args::parse();
    let config = read_config(&args)?;

    let (events_sink, events_source) = mpsc::unbounded_channel();
    let monitor = tokio::spawn(EventMonitor::new(&config, events_source, args.output).run());
    pin!(monitor);

    let clock_coordinator = ClockCoordinator::new();
    let clock = clock_coordinator.clock();
    let tracker = EventTracker::new(events_sink, clock.clone(), &config.nodes);
    let mut simulation = Simulation::new(config, tracker, clock_coordinator).await?;

    select! {
        result = simulation.run(token) => { result? }
        result = &mut monitor => { result?? }
        _ = ctrlc_source => {}
    };

    simulation.shutdown()?;
    monitor.await??;
    Ok(())
}

#[cfg(test)]
mod tests {
    use anyhow::Result;
    use std::fs;

    use crate::{read_config, Args};

    #[test]
    fn should_parse_topologies() -> Result<()> {
        let topology_dir = concat!(env!("CARGO_MANIFEST_DIR"), "/../test_data");
        for topology in fs::read_dir(topology_dir)? {
            let args = Args {
                topology: Some(topology?.path()),
                output: None,
                parameters: vec![],
                timescale: None,
                trace_node: vec![],
                slots: None,
                conformance_events: false,
                aggregate_events: false,
            };
            read_config(&args)?;
        }
        Ok(())
    }
}
