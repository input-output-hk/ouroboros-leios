use std::{collections::BTreeMap, path::PathBuf};

use anyhow::Result;
use serde::Serialize;
use sim_core::{
    clock::Timestamp,
    config::{NodeId, SimConfiguration},
    events::Event,
    model::TransactionId,
};
use tokio::{fs::File, io::AsyncWriteExt as _, sync::mpsc};
use tracing::{info, info_span};

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
        publisher: NodeId,
        bytes: u64,
    },
    TransactionReceived {
        time: Timestamp,
        id: TransactionId,
        sender: NodeId,
        recipient: NodeId,
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

pub struct EventMonitor {
    node_ids: Vec<NodeId>,
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
        let node_ids = config.nodes.iter().map(|p| p.id).collect();
        let pool_ids = config
            .nodes
            .iter()
            .filter(|p| p.stake > 0)
            .map(|p| p.id)
            .collect();
        Self {
            node_ids,
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
        let mut seen_ibs: BTreeMap<NodeId, u64> = BTreeMap::new();

        let mut filled_slots = 0u64;
        let mut empty_slots = 0u64;
        let mut published_txs = 0u64;
        let mut published_bytes = 0u64;
        let mut generated_ibs = 0u64;
        let mut total_txs = 0u64;

        let mut output = match self.output_path {
            Some(ref path) => OutputTarget::File(File::create(path).await?),
            None => OutputTarget::None,
        };
        while let Some((event, timestamp)) = self.events_source.recv().await {
            self.compute_output_events(&mut output, &event, timestamp)
                .await?;
            match event {
                Event::Transaction { id, bytes, .. } => {
                    total_txs += 1;
                    pending_tx_sizes.insert(id, bytes);
                }
                Event::TransactionReceived { .. } => {}
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
                    *seen_ibs.entry(block.header.producer).or_default() += 1;
                    info!(
                        "Pool {} generated an IB with {} transaction(s) in slot {}",
                        block.header.producer,
                        block.transactions.len(),
                        block.header.slot,
                    )
                }
                Event::InputBlockReceived { recipient, .. } => {
                    *seen_ibs.entry(recipient).or_default() += 1;
                }
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
            let avg_seen = self
                .node_ids
                .iter()
                .map(|id| seen_ibs.get(id).copied().unwrap_or_default() as f64)
                .sum::<f64>()
                / self.node_ids.len() as f64;
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
            info!("Each node received an average of {avg_seen} IBs.");
        });
        Ok(())
    }

    async fn compute_output_events(
        &self,
        output: &mut OutputTarget,
        event: &Event,
        time: Timestamp,
    ) -> Result<()> {
        match event {
            Event::Slot { number, block } => {
                if let Some(block) = block {
                    output
                        .write(OutputEvent::PraosBlockGenerated {
                            time,
                            slot: *number,
                            producer: block.producer,
                            transactions: block.transactions.iter().map(|t| t.id).collect(),
                        })
                        .await?;
                }
            }
            Event::Transaction {
                id,
                publisher,
                bytes,
            } => {
                output
                    .write(OutputEvent::TransactionCreated {
                        time,
                        id: *id,
                        publisher: *publisher,
                        bytes: *bytes,
                    })
                    .await?;
            }
            Event::TransactionReceived {
                id,
                sender,
                recipient,
            } => {
                output
                    .write(OutputEvent::TransactionReceived {
                        time,
                        id: *id,
                        sender: *sender,
                        recipient: *recipient,
                    })
                    .await?;
            }
            Event::BlockReceived {
                slot,
                sender,
                recipient,
            } => {
                output
                    .write(OutputEvent::PraosBlockReceived {
                        time,
                        slot: *slot,
                        sender: *sender,
                        recipient: *recipient,
                    })
                    .await?;
            }
            Event::InputBlockGenerated { block } => {
                output
                    .write(OutputEvent::InputBlockGenerated {
                        time,
                        slot: block.header.slot,
                        producer: block.header.producer,
                        index: block.header.index,
                        transactions: block.transactions.iter().map(|t| t.id).collect(),
                    })
                    .await?;
            }
            Event::InputBlockReceived {
                block,
                sender,
                recipient,
            } => {
                output
                    .write(OutputEvent::InputBlockReceived {
                        time,
                        slot: block.header.slot,
                        producer: block.header.producer,
                        index: block.header.index,
                        sender: *sender,
                        recipient: *recipient,
                    })
                    .await?;
            }
        }
        Ok(())
    }
}

enum OutputTarget {
    File(File),
    None,
}

impl OutputTarget {
    async fn write(&mut self, event: OutputEvent) -> Result<()> {
        let Self::File(file) = self else {
            return Ok(());
        };
        let mut string = serde_json::to_string(&event)?;
        string.push('\n');
        file.write_all(string.as_bytes()).await?;
        Ok(())
    }
}
