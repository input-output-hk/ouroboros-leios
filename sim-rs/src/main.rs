use std::{collections::BTreeMap, path::PathBuf, process};

use anyhow::Result;
use clap::Parser;
use config::{read_config, PoolId, SimConfiguration};
use events::{Event, EventTracker};
use sim::Simulation;
use tokio::{
    pin, select,
    sync::{mpsc, oneshot},
};
use tracing::{info, warn};

mod config;
mod events;
mod sim;

// Monitor and report any events emitted by the simulation,
// including any aggregated stats at the end.
async fn monitor_events(
    config: SimConfiguration,
    mut events_source: mpsc::UnboundedReceiver<Event>,
) -> Result<()> {
    let pool_ids: Vec<PoolId> = config.pools.iter().map(|pool| pool.id).collect();

    let mut blocks_published: BTreeMap<PoolId, u64> = BTreeMap::new();
    let mut blocks_rejected: BTreeMap<PoolId, u64> = BTreeMap::new();
    let mut filled_slots = 0u64;
    let mut empty_slots = 0u64;

    while let Some(event) = events_source.recv().await {
        match event {
            Event::Slot {
                number,
                publisher,
                conflicts,
            } => {
                if let Some(publisher) = publisher {
                    info!("Pool {publisher} published a block in slot {number}.");
                    filled_slots += 1;
                    *blocks_published.entry(publisher).or_default() += 1;
                } else {
                    info!("No pools published a block in slot {number}.");
                    empty_slots += 1;
                }
                for conflict in conflicts {
                    *blocks_rejected.entry(conflict).or_default() += 1;
                }
            }
        }
    }

    info!("{filled_slots} block(s) were published.");
    info!("{empty_slots} slot(s) had no blocks.");
    for id in pool_ids {
        let published = blocks_published.get(&id).copied().unwrap_or_default();
        info!("Pool {id} published {published} block(s)");
        let rejected = blocks_rejected.get(&id).copied().unwrap_or_default();
        info!("Pool {id} failed to publish {rejected} block(s) due to conflicts.");
    }

    Ok(())
}

#[derive(Parser)]
struct Args {
    filename: PathBuf,
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
    let config = read_config(&args.filename)?;

    let (events_sink, events_source) = mpsc::unbounded_channel();
    let monitor = monitor_events(config.clone(), events_source);
    pin!(monitor);

    let tracker = EventTracker::new(events_sink);
    let simulation = Simulation::new(config);

    select! {
        _ = simulation.run(tracker) => {}
        result = &mut monitor => { result? }
        _ = ctrlc_source => {}
    };

    monitor.await?;
    Ok(())
}
