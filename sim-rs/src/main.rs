use std::{path::PathBuf, process, time::Instant};

use anyhow::Result;
use clap::Parser;
use clock::Clock;
use config::read_config;
use events::{EventMonitor, EventTracker};
use sim::Simulation;
use tokio::{
    pin, select,
    sync::{mpsc, oneshot},
};
use tracing::warn;

mod clock;
mod config;
mod events;
mod network;
mod probability;
mod sim;

#[derive(Parser)]
struct Args {
    filename: PathBuf,
    output: Option<PathBuf>,
    #[clap(short, long)]
    timescale: Option<u32>,
}

#[tokio::main]
async fn main() -> Result<()> {
    tracing_subscriber::fmt().compact().without_time().init();

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
    let config = read_config(&args.filename, args.timescale)?;

    let (events_sink, events_source) = mpsc::unbounded_channel();
    let monitor = EventMonitor::new(&config, events_source, args.output).run();
    pin!(monitor);

    let clock = Clock::new(Instant::now(), config.timescale);
    let tracker = EventTracker::new(events_sink, clock.clone());
    let mut simulation = Simulation::new(config, clock)?;

    select! {
        result = simulation.run(tracker) => { result? }
        result = &mut monitor => { result? }
        _ = ctrlc_source => {}
    };

    simulation.shutdown()?;
    monitor.await?;
    Ok(())
}
