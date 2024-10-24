use std::{
    collections::{BTreeMap, BTreeSet},
    path::PathBuf,
};

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
struct OutputEvent {
    time: Timestamp,
    #[serde(flatten)]
    event: Event,
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
        let mut tx_sizes: BTreeMap<TransactionId, u64> = BTreeMap::new();
        let mut pending_txs: BTreeSet<TransactionId> = BTreeSet::new();
        let mut tx_ib_counts: BTreeMap<TransactionId, u64> = BTreeMap::new();
        let mut seen_ibs: BTreeMap<NodeId, u64> = BTreeMap::new();

        let mut filled_slots = 0u64;
        let mut max_slot = 0u64;
        let mut published_txs = 0u64;
        let mut published_bytes = 0u64;
        let mut generated_ibs = 0u64;
        let mut total_txs = 0u64;

        let mut output = match self.output_path {
            Some(ref path) => OutputTarget::File(File::create(path).await?),
            None => OutputTarget::None,
        };
        while let Some((event, time)) = self.events_source.recv().await {
            let output_event = OutputEvent {
                time,
                event: event.clone(),
            };
            output.write(output_event).await?;
            match event {
                Event::Slot { number } => {
                    info!("Slot {number} has begun.");
                    max_slot = number;
                }
                Event::TransactionGenerated { id, bytes, .. } => {
                    total_txs += 1;
                    tx_sizes.insert(id, bytes);
                    pending_txs.insert(id);
                }
                Event::TransactionReceived { .. } => {}
                Event::PraosBlockGenerated {
                    slot,
                    producer,
                    transactions,
                    conflicts,
                } => {
                    info!("Pool {} produced a block in slot {slot}.", producer);
                    filled_slots += 1;
                    for published_tx in transactions {
                        let tx_bytes = tx_sizes.get(&published_tx).unwrap();
                        published_txs += 1;
                        published_bytes += tx_bytes;
                        pending_txs.remove(&published_tx);
                    }
                    *blocks_published.entry(producer).or_default() += 1;

                    for conflict in conflicts {
                        *blocks_rejected.entry(conflict).or_default() += 1;
                    }
                }
                Event::PraosBlockReceived { .. } => {}
                Event::InputBlockGenerated {
                    header,
                    transactions,
                } => {
                    generated_ibs += 1;
                    for tx in &transactions {
                        *tx_ib_counts.entry(*tx).or_default() += 1;
                    }
                    *seen_ibs.entry(header.producer).or_default() += 1;
                    info!(
                        "Pool {} generated an IB with {} transaction(s) in slot {}",
                        header.producer,
                        transactions.len(),
                        header.slot,
                    )
                }
                Event::InputBlockReceived { recipient, .. } => {
                    *seen_ibs.entry(recipient).or_default() += 1;
                }
            }
        }

        info_span!("praos").in_scope(|| {
            info!("{filled_slots} block(s) were published.");
            info!("{} slot(s) had no blocks.", max_slot - filled_slots);
            info!("{published_txs} transaction(s) ({published_bytes} byte(s)) made it on-chain.");
            info!(
                "{} transaction(s) ({} byte(s)) did not reach a block.",
                pending_txs.len(),
                pending_txs
                    .iter()
                    .filter_map(|id| tx_sizes.get(id))
                    .sum::<u64>(),
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
                generated_ibs as f64 / (max_slot) as f64
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
