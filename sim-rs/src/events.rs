use std::{collections::BTreeMap, fs, path::PathBuf, time::Instant};

use anyhow::Result;
use serde::Serialize;
use tokio::sync::mpsc;
use tracing::{info, warn};

use crate::config::{PoolId, SimConfiguration};

pub enum Event {
    Slot { number: u64, block: Option<Block> },
    Transaction { id: u64, bytes: u64 },
}
pub struct Block {
    pub publisher: PoolId,
    pub conflicts: Vec<PoolId>,
    pub transactions: Vec<Transaction>,
}

#[derive(Debug, Clone)]
pub struct Transaction {
    pub id: u64,
    pub bytes: u64,
}

#[derive(Clone, Serialize)]
enum OutputEvent {
    BlockGenerated {
        time: u128,
        slot: u64,
        publisher: PoolId,
        transactions: Vec<u64>,
    },
    TransactionCreated {
        time: u128,
        id: u64,
        bytes: u64,
    },
}

#[derive(Clone)]
pub struct EventTracker(mpsc::UnboundedSender<(Event, Instant)>);

impl EventTracker {
    pub fn new(inner: mpsc::UnboundedSender<(Event, Instant)>) -> Self {
        Self(inner)
    }

    pub fn track_slot(&self, number: u64, block: Option<Block>) {
        self.send(Event::Slot { number, block });
    }

    pub fn track_transaction(&self, transaction: &Transaction) {
        self.send(Event::Transaction {
            id: transaction.id,
            bytes: transaction.bytes,
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
        let mut pending_tx_sizes: BTreeMap<u64, u64> = BTreeMap::new();

        let mut filled_slots = 0u64;
        let mut empty_slots = 0u64;
        let mut published_txs = 0u64;
        let mut published_bytes = 0u64;

        let mut output = vec![];
        while let Some((event, timestamp)) = self.events_source.recv().await {
            self.compute_output_events(&mut output, &event, timestamp);
            match event {
                Event::Slot { number, block } => {
                    if let Some(block) = block {
                        info!(
                            "Pool {} published a block in slot {number}.",
                            block.publisher
                        );
                        filled_slots += 1;
                        for published_tx in block.transactions {
                            published_txs += 1;
                            published_bytes += published_tx.bytes;
                            pending_tx_sizes.remove(&published_tx.id);
                        }
                        *blocks_published.entry(block.publisher).or_default() += 1;

                        for conflict in block.conflicts {
                            *blocks_rejected.entry(conflict).or_default() += 1;
                        }
                    } else {
                        info!("No pools published a block in slot {number}.");
                        empty_slots += 1;
                    }
                }
                Event::Transaction { id, bytes } => {
                    pending_tx_sizes.insert(id, bytes);
                }
            }
        }

        info!("{filled_slots} block(s) were published.");
        info!("{empty_slots} slot(s) had no blocks.");
        info!("{published_txs} transaction(s) ({published_bytes} byte(s)) made it on-chain.");

        info!(
            "{} transaction(s) ({} byte(s)) did not reach a block.",
            pending_tx_sizes.len(),
            pending_tx_sizes.into_values().sum::<u64>()
        );

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
            Event::Slot { number, block } => {
                if let Some(block) = block {
                    output.push(OutputEvent::BlockGenerated {
                        time,
                        slot: *number,
                        publisher: block.publisher,
                        transactions: block.transactions.iter().map(|t| t.id).collect(),
                    });
                }
            }
            Event::Transaction { id, bytes } => {
                output.push(OutputEvent::TransactionCreated {
                    time,
                    id: *id,
                    bytes: *bytes,
                });
            }
        }
    }
}
