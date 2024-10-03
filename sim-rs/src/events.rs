use std::{collections::BTreeMap, fs, path::PathBuf, time::Instant};

use anyhow::Result;
use serde::Serialize;
use tokio::sync::mpsc;
use tracing::{info, warn};

use crate::config::{PoolId, SimConfiguration};

pub enum Event {
    Slot {
        number: u64,
        publisher: Option<PoolId>,
        conflicts: Vec<PoolId>,
    },
}

#[derive(Clone, Serialize)]
enum OutputEvent {
    BlockGenerated {
        time: u128,
        slot: u64,
        publisher: PoolId,
    },
}

#[derive(Clone)]
pub struct EventTracker(mpsc::UnboundedSender<(Event, Instant)>);

impl EventTracker {
    pub fn new(inner: mpsc::UnboundedSender<(Event, Instant)>) -> Self {
        Self(inner)
    }

    pub fn track_slot(&self, number: u64, publisher: Option<PoolId>, conflicts: Vec<PoolId>) {
        self.send(Event::Slot {
            number,
            publisher,
            conflicts,
        });
    }

    fn send(&self, event: Event) {
        if self.0.send((event, Instant::now())).is_err() {
            warn!("tried sending event after aggregator finished");
        }
    }
}

pub struct EventMonitor {
    pool_ids: Vec<PoolId>,
    start: Instant,
    events_source: mpsc::UnboundedReceiver<(Event, Instant)>,
    output_path: Option<PathBuf>,
}

impl EventMonitor {
    pub fn new(
        config: &SimConfiguration,
        events_source: mpsc::UnboundedReceiver<(Event, Instant)>,
        output_path: Option<PathBuf>,
    ) -> Self {
        let pool_ids = config.pools.iter().map(|p| p.id).collect();
        let start = Instant::now();
        Self {
            pool_ids,
            start,
            events_source,
            output_path,
        }
    }

    // Monitor and report any events emitted by the simulation,
    // including any aggregated stats at the end.
    pub async fn run(mut self) -> Result<()> {
        let mut blocks_published: BTreeMap<PoolId, u64> = BTreeMap::new();
        let mut blocks_rejected: BTreeMap<PoolId, u64> = BTreeMap::new();
        let mut filled_slots = 0u64;
        let mut empty_slots = 0u64;

        let mut output = vec![];
        while let Some((event, timestamp)) = self.events_source.recv().await {
            self.compute_output_events(&mut output, &event, timestamp);
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
        for id in self.pool_ids {
            let published = blocks_published.get(&id).copied().unwrap_or_default();
            info!("Pool {id} published {published} block(s)");
            let rejected = blocks_rejected.get(&id).copied().unwrap_or_default();
            info!("Pool {id} failed to publish {rejected} block(s) due to conflicts.");
        }

        if let Some(path) = self.output_path {
            fs::write(path, serde_json::to_vec(&output)?)?;
        }
        Ok(())
    }

    fn compute_output_events(
        &self,
        output: &mut Vec<OutputEvent>,
        event: &Event,
        timestamp: Instant,
    ) {
        let time = timestamp.duration_since(self.start).as_nanos();
        match event {
            Event::Slot {
                number, publisher, ..
            } => {
                if let Some(publisher) = publisher {
                    output.push(OutputEvent::BlockGenerated {
                        time,
                        slot: *number,
                        publisher: *publisher,
                    });
                }
            }
        }
    }
}
