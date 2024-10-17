use std::{collections::BTreeMap, fs, path::PathBuf, sync::Arc};

use anyhow::Result;
use serde::Serialize;
use tokio::sync::mpsc;
use tracing::{info, info_span, warn};

use crate::{
    clock::{Clock, Timestamp},
    config::{NodeId, SimConfiguration},
    model::{Block, InputBlock, Transaction, TransactionId},
};

pub enum Event {
    Transaction {
        id: TransactionId,
        bytes: u64,
    },
    Slot {
        number: u64,
        block: Option<Block>,
    },
    BlockReceived {
        slot: u64,
        sender: NodeId,
        recipient: NodeId,
    },
    InputBlockGenerated {
        block: Arc<InputBlock>,
    },
    InputBlockReceived {
        block: Arc<InputBlock>,
        sender: NodeId,
        recipient: NodeId,
    },
}

#[derive(Clone, Serialize)]
enum OutputEvent {
    PraosBlockGenerated {
        time: Timestamp,
        slot: u64,
        producer: NodeId,
        transactions: Vec<TransactionId>,
    },
    PraosBlockReceived {
        time: Timestamp,
        slot: u64,
        sender: NodeId,
        recipient: NodeId,
    },
    TransactionCreated {
        time: Timestamp,
        id: TransactionId,
        bytes: u64,
    },
    InputBlockGenerated {
        time: Timestamp,
        slot: u64,
        producer: NodeId,
        index: u64,
        transactions: Vec<TransactionId>,
    },
    InputBlockReceived {
        time: Timestamp,
        slot: u64,
        producer: NodeId,
        index: u64,
        sender: NodeId,
        recipient: NodeId,
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

    pub fn track_ib_generated(&self, block: Arc<InputBlock>) {
        self.send(Event::InputBlockGenerated { block });
    }

    pub fn track_ib_received(&self, block: Arc<InputBlock>, sender: NodeId, recipient: NodeId) {
        self.send(Event::InputBlockReceived {
            block,
            sender,
            recipient,
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
        let mut pending_tx_sizes: BTreeMap<TransactionId, u64> = BTreeMap::new();
        let mut tx_ib_counts: BTreeMap<TransactionId, u64> = BTreeMap::new();

        let mut filled_slots = 0u64;
        let mut empty_slots = 0u64;
        let mut published_txs = 0u64;
        let mut published_bytes = 0u64;
        let mut generated_ibs = 0u64;
        let mut total_txs = 0u64;

        let mut output = vec![];
        while let Some((event, timestamp)) = self.events_source.recv().await {
            self.compute_output_events(&mut output, &event, timestamp);
            match event {
                Event::Transaction { id, bytes } => {
                    total_txs += 1;
                    pending_tx_sizes.insert(id, bytes);
                }
                Event::Slot { number, block } => {
                    if let Some(block) = block {
                        info!("Pool {} produced a block in slot {number}.", block.producer);
                        filled_slots += 1;
                        for published_tx in block.transactions {
                            published_txs += 1;
                            published_bytes += published_tx.bytes;
                            pending_tx_sizes.remove(&published_tx.id);
                        }
                        *blocks_published.entry(block.producer).or_default() += 1;

                        for conflict in block.conflicts {
                            *blocks_rejected.entry(conflict).or_default() += 1;
                        }
                    } else {
                        info!("No pools published a block in slot {number}.");
                        empty_slots += 1;
                    }
                }
                Event::BlockReceived { .. } => {}
                Event::InputBlockGenerated { block } => {
                    generated_ibs += 1;
                    for tx in &block.transactions {
                        *tx_ib_counts.entry(tx.id).or_default() += 1;
                    }
                    info!(
                        "Pool {} generated an IB with {} transaction(s) in slot {}",
                        block.header.producer,
                        block.transactions.len(),
                        block.header.slot,
                    )
                }
                Event::InputBlockReceived { .. } => {}
            }
        }

        info_span!("praos").in_scope(|| {
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
        });

        info_span!("leios").in_scope(|| {
            let txs_in_ib: u64 = tx_ib_counts.values().copied().sum();
            info!(
                "{generated_ibs} IB(s) were generated, on average {} per slot.",
                generated_ibs as f64 / (filled_slots + empty_slots) as f64
            );
            info!(
                "{} out of {} transaction(s) reached an IB.",
                tx_ib_counts.len(),
                total_txs
            );
            info!(
                "Each transaction was included in an average of {} IBs.",
                txs_in_ib as f64 / total_txs as f64
            );
            info!(
                "Each IB contained an average of {} transactions.",
                txs_in_ib as f64 / generated_ibs as f64
            );
        });

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
                    output.push(OutputEvent::PraosBlockGenerated {
                        time,
                        slot: *number,
                        producer: block.producer,
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
                output.push(OutputEvent::PraosBlockReceived {
                    time,
                    slot: *slot,
                    sender: *sender,
                    recipient: *recipient,
                });
            }
            Event::InputBlockGenerated { block } => {
                output.push(OutputEvent::InputBlockGenerated {
                    time,
                    slot: block.header.slot,
                    producer: block.header.producer,
                    index: block.header.index,
                    transactions: block.transactions.iter().map(|t| t.id).collect(),
                });
            }
            Event::InputBlockReceived {
                block,
                sender,
                recipient,
            } => {
                output.push(OutputEvent::InputBlockReceived {
                    time,
                    slot: block.header.slot,
                    producer: block.header.producer,
                    index: block.header.index,
                    sender: *sender,
                    recipient: *recipient,
                });
            }
        }
    }
}
