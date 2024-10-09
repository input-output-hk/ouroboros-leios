use std::{collections::BTreeMap, fs, path::PathBuf};

use anyhow::Result;
use serde::Serialize;
use tokio::sync::mpsc;
use tracing::{info, warn};

use crate::{
    clock::{Clock, Timestamp},
    config::{NodeId, SimConfiguration},
};

pub enum Event {
    Slot {
        number: u64,
        block: Option<Block>,
    },
    BlockReceived {
        slot: u64,
        sender: NodeId,
        recipient: NodeId,
    },
    Transaction {
        id: u64,
        bytes: u64,
    },
}

#[derive(Clone, PartialEq, Eq)]
pub struct Block {
    pub slot: u64,
    pub publisher: NodeId,
    pub conflicts: Vec<NodeId>,
    pub transactions: Vec<Transaction>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Transaction {
    pub id: u64,
    pub bytes: u64,
}

#[derive(Clone, Serialize)]
enum OutputEvent {
    BlockGenerated {
        time: Timestamp,
        slot: u64,
        publisher: NodeId,
        transactions: Vec<u64>,
    },
    BlockReceived {
        time: Timestamp,
        slot: u64,
        sender: NodeId,
        recipient: NodeId,
    },
    TransactionCreated {
        time: Timestamp,
        id: u64,
        bytes: u64,
    },
}

#[derive(Clone)]
pub struct EventTracker {
    sender: mpsc::UnboundedSender<(Event, Timestamp)>,
    clock: Clock,
}

impl EventTracker {
    pub fn new(sender: mpsc::UnboundedSender<(Event, Timestamp)>, clock: Clock) -> Self {
        Self { sender, clock }
    }

    pub fn track_slot(&self, number: u64, block: Option<Block>) {
        self.send(Event::Slot { number, block });
    }

    pub fn track_block_received(&self, slot: u64, sender: NodeId, recipient: NodeId) {
        self.send(Event::BlockReceived {
            slot,
            sender,
            recipient,
        });
    }

    pub fn track_transaction(&self, transaction: &Transaction) {
        self.send(Event::Transaction {
            id: transaction.id,
            bytes: transaction.bytes,
        });
    }

    fn send(&self, event: Event) {
        if self.sender.send((event, self.clock.now())).is_err() {
            warn!("tried sending event after aggregator finished");
        }
    }
}

pub struct EventMonitor {
    pool_ids: Vec<NodeId>,
    events_source: mpsc::UnboundedReceiver<(Event, Timestamp)>,
    output_path: Option<PathBuf>,
}

impl EventMonitor {
    pub fn new(
        config: &SimConfiguration,
        events_source: mpsc::UnboundedReceiver<(Event, Timestamp)>,
        output_path: Option<PathBuf>,
    ) -> Self {
        let pool_ids = config
            .nodes
            .iter()
            .filter(|p| p.stake > 0)
            .map(|p| p.id)
            .collect();
        Self {
            pool_ids,
            events_source,
            output_path,
        }
    }

    // Monitor and report any events emitted by the simulation,
    // including any aggregated stats at the end.
    pub async fn run(mut self) -> Result<()> {
        let mut blocks_published: BTreeMap<NodeId, u64> = BTreeMap::new();
        let mut blocks_rejected: BTreeMap<NodeId, u64> = BTreeMap::new();
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
                Event::BlockReceived { .. } => {}
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
            if let Some(published) = blocks_published.get(&id) {
                info!("Pool {id} published {published} block(s)");
            }
            if let Some(rejected) = blocks_rejected.get(&id) {
                info!("Pool {id} failed to publish {rejected} block(s) due to conflicts.");
            }
        }

        if let Some(path) = self.output_path {
            if let Some(parent) = path.parent() {
                fs::create_dir_all(parent)?;
            }
            fs::write(path, serde_json::to_vec(&output)?)?;
        }
        Ok(())
    }

    fn compute_output_events(&self, output: &mut Vec<OutputEvent>, event: &Event, time: Timestamp) {
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
            Event::BlockReceived {
                slot,
                sender,
                recipient,
            } => {
                output.push(OutputEvent::BlockReceived {
                    time,
                    slot: *slot,
                    sender: *sender,
                    recipient: *recipient,
                });
            }
        }
    }
}
