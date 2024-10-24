use std::{path::PathBuf, process, time::Instant};

use anyhow::Result;
use clap::Parser;
use config::read_config;
use events::EventMonitor;
use sim_core::{clock::Clock, events::EventTracker, sim::Simulation};
use tokio::{
    pin, select,
    sync::{mpsc, oneshot},
};
use tracing::{level_filters::LevelFilter, warn};
use tracing_subscriber::{layer::SubscriberExt as _, util::SubscriberInitExt, EnvFilter};

mod config;
mod events;

#[derive(Parser)]
struct Args {
    filename: PathBuf,
    output: Option<PathBuf>,
    #[clap(short, long)]
    timescale: Option<u32>,
    #[clap(long)]
    trace_node: Vec<usize>,
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

    // Handle ctrl+c (SIGINT) at an application level, so we can report on necessary stats before shutting down.
    let (ctrlc_sink, ctrlc_source) = oneshot::channel();
    let mut ctrlc_sink = Some(ctrlc_sink);
    ctrlc::set_handler(move || {
        if let Some(sink) = ctrlc_sink.take() {
            let _ = sink.send(());
        } else {
            warn!("force quitting");
            process::exit(0);
        }
    })?;

    let args = Args::parse();
    let config = read_config(&args.filename, args.timescale, &args.trace_node)?;

    let (events_sink, events_source) = mpsc::unbounded_channel();
    let monitor = EventMonitor::new(&config, events_source, args.output).run();
    pin!(monitor);

    let clock = Clock::new(Instant::now(), config.timescale);
    let tracker = EventTracker::new(events_sink, clock.clone());
    let mut simulation = Simulation::new(config, tracker, clock)?;

    select! {
        result = simulation.run() => { result? }
        result = &mut monitor => { result? }
        _ = ctrlc_source => {}
    };

    simulation.shutdown()?;
    monitor.await?;
    Ok(())
}
