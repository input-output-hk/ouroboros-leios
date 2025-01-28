use std::{fs, path::PathBuf, process};

use anyhow::Result;
use clap::Parser;
use events::{EventMonitor, OutputFormat};
use figment::{
    providers::{Format as _, Yaml},
    Figment,
};
use sim_core::{
    clock::ClockCoordinator,
    config::{NodeId, RawLegacyTopology, RawParameters, RawTopology, SimConfiguration, Topology},
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

#[derive(Parser)]
struct Args {
    topology: PathBuf,
    output: Option<PathBuf>,
    #[clap(short, long)]
    parameters: Vec<PathBuf>,
    #[clap(short, long)]
    format: Option<OutputFormat>,
    #[clap(short, long)]
    timescale: Option<f64>,
    #[clap(long)]
    trace_node: Vec<usize>,
    #[clap(short, long)]
    slots: Option<u64>,
}

fn read_config(args: &Args) -> Result<SimConfiguration> {
    let topology_str = fs::read_to_string(&args.topology)?;
    let topology_ext = args.topology.extension().and_then(|ext| ext.to_str());
    let topology: Topology = if topology_ext == Some("toml") {
        let raw_topology: RawLegacyTopology = toml::from_str(&topology_str)?;
        raw_topology.into()
    } else {
        let raw_topology: RawTopology = serde_yaml::from_str(&topology_str)?;
        raw_topology.into()
    };
    topology.validate()?;

    let mut raw_params = Figment::new().merge(Yaml::string(include_str!(
        "../../../data/simulation/config.default.yaml"
    )));

    for params_file in &args.parameters {
        raw_params = raw_params.merge(Yaml::file_exact(params_file));
    }

    let params: RawParameters = raw_params.extract()?;
    let mut config = SimConfiguration::build(params, topology);
    if let Some(slots) = args.slots {
        config.slots = Some(slots);
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
    let monitor =
        tokio::spawn(EventMonitor::new(&config, events_source, args.output, args.format).run());
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
                topology: topology?.path(),
                output: None,
                parameters: vec![],
                format: None,
                timescale: None,
                trace_node: vec![],
                slots: None,
            };
            read_config(&args)?;
        }
        Ok(())
    }
}
