use std::{fs, path::PathBuf, process, time::Instant};

use anyhow::Result;
use clap::Parser;
use events::{EventMonitor, OutputFormat};
use sim_core::{
    clock::Clock,
    config::{NodeId, RawConfig, SimConfiguration},
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
    filename: PathBuf,
    output: Option<PathBuf>,
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
    let file = fs::read_to_string(&args.filename)?;
    let mut raw_config: RawConfig = toml::from_str(&file)?;
    if let Some(slots) = args.slots {
        raw_config.slots = Some(slots);
    }
    if let Some(ts) = args.timescale {
        raw_config.timescale = Some(ts);
    }
    for id in &args.trace_node {
        raw_config.trace_nodes.insert(NodeId::new(*id));
    }
    let config: SimConfiguration = raw_config.into();
    config.validate()?;
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

    let clock = Clock::new(Instant::now(), config.timescale);
    let tracker = EventTracker::new(events_sink, clock.clone());
    let mut simulation = Simulation::new(config, tracker, clock)?;

    select! {
        result = simulation.run(token) => { result? }
        result = &mut monitor => { result?? }
        _ = ctrlc_source => {}
    };

    simulation.shutdown()?;
    monitor.await??;
    Ok(())
}
