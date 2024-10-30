use std::{
    collections::{BTreeMap, BTreeSet},
    path::PathBuf, time::Duration,
};

use anyhow::Result;
use average::Variance;
use pretty_bytes_rust::{pretty_bytes, PrettyBytesOptions};
use serde::Serialize;
use sim_core::{
    clock::Timestamp,
    config::{NodeId, SimConfiguration},
    events::Event,
    model::{InputBlockId, TransactionId},
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
        let mut blocks: BTreeMap<u64, (NodeId, u64)> = BTreeMap::new();
        let mut txs: BTreeMap<TransactionId, Transaction> = BTreeMap::new();
        let mut pending_txs: BTreeSet<TransactionId> = BTreeSet::new();
        let mut seen_ibs: BTreeMap<NodeId, f64> = BTreeMap::new();
        let mut txs_in_ib: BTreeMap<InputBlockId, f64> = BTreeMap::new();
        let mut bytes_in_ib: BTreeMap<InputBlockId, f64> = BTreeMap::new();
        let mut ibs_containing_tx: BTreeMap<TransactionId, f64> = BTreeMap::new();

        let mut last_timestamp = Timestamp(Duration::from_secs(0));
        let mut total_slots = 0u64;
        let mut published_txs = 0u64;
        let mut published_bytes = 0u64;
        let mut generated_ibs = 0u64;
        let mut empty_ibs = 0u64;

        // Pretty print options for bytes
        let pbo = Some(PrettyBytesOptions {
            use_1024_instead_of_1000: Some(false),
            number_of_decimal: Some(2),
            remove_zero_decimal: Some(true),
        });

        let mut output = match self.output_path {
            Some(ref path) => OutputTarget::File(File::create(path).await?),
            None => OutputTarget::None,
        };
        while let Some((event, time)) = self.events_source.recv().await {
            last_timestamp = time.clone();
            if should_log_event(&event) {
                let output_event = OutputEvent {
                    time,
                    event: event.clone(),
                };
                output.write(output_event).await?;
            }
            match event {
                Event::Slot { number } => {
                    info!("Slot {number} has begun.");
                    total_slots = number + 1;
                }
                Event::TransactionGenerated { id, bytes, .. } => {
                    txs.insert(
                        id,
                        Transaction {
                            bytes,
                            generated: time,
                            included_in_ib: None,
                        },
                    );
                    pending_txs.insert(id);
                }
                Event::TransactionReceived { .. } => {}
                Event::PraosBlockGenerated {
                    slot,
                    producer,
                    vrf,
                    transactions,
                } => {
                    info!("Pool {} produced a praos block in slot {slot}.", producer);
                    if let Some((old_producer, old_vrf)) = blocks.get(&slot) {
                        if *old_vrf > vrf {
                            *blocks_published.entry(producer).or_default() += 1;
                            *blocks_published.entry(*old_producer).or_default() -= 1;
                            *blocks_rejected.entry(*old_producer).or_default() += 1;
                            blocks.insert(slot, (producer, vrf));
                        } else {
                            *blocks_rejected.entry(producer).or_default() += 1;
                        }
                    } else {
                        *blocks_published.entry(producer).or_default() += 1;
                        blocks.insert(slot, (producer, vrf));
                    }
                    for published_tx in transactions {
                        let tx = txs.get(&published_tx).unwrap();
                        published_txs += 1;
                        published_bytes += tx.bytes;
                        pending_txs.remove(&published_tx);
                    }
                    *blocks_published.entry(producer).or_default() += 1;
                }
                Event::PraosBlockReceived { .. } => {}
                Event::InputBlockGenerated {
                    header,
                    transactions,
                } => {
                    generated_ibs += 1;
                    let mut ib_bytes = 0;
                    for tx_id in &transactions {
                        *txs_in_ib.entry(header.id()).or_default() += 1.;
                        *ibs_containing_tx.entry(*tx_id).or_default() += 1.;
                        let tx = txs.get_mut(tx_id).unwrap();
                        ib_bytes += tx.bytes;
                        *bytes_in_ib.entry(header.id()).or_default() += tx.bytes as f64;
                        if tx.included_in_ib.is_none() {
                            tx.included_in_ib = Some(time);
                        }
                    }
                    *seen_ibs.entry(header.producer).or_default() += 1.;
                    info!(
                        "Pool {} generated an IB with {} transaction(s) in slot {} ({})",
                        header.producer,
                        transactions.len(),
                        header.slot,
                        pretty_bytes(ib_bytes, pbo.clone()),
                    )
                }
                Event::EmptyInputBlockNotGenerated { .. } => {
                    empty_ibs += 1;
                }
                Event::InputBlockReceived { recipient, .. } => {
                    *seen_ibs.entry(recipient).or_default() += 1.;
                }
            }
        }

        info_span!("praos").in_scope(|| {
            info!("{} transactions(s) were generated in total.", txs.len());
            info!("{} naive praos block(s) were published.", blocks.len());
            info!(
                "{} slot(s) had no naive praos blocks.",
                total_slots - blocks.len() as u64
            );
            info!("{published_txs} transaction(s) ({}) finalized in a naive praos block.", pretty_bytes(published_bytes, pbo.clone()));
            info!(
                "{} transaction(s) ({}) did not reach a naive praos block.",
                pending_txs.len(),
                pretty_bytes(
                    pending_txs
                        .iter()
                        .filter_map(|id| txs.get(id))
                        .map(|tx| tx.bytes)
                        .sum::<u64>(),
                    pbo.clone(),
                ),
            );

            for id in self.pool_ids {
                if let Some(published) = blocks_published.get(&id) {
                    info!("Pool {id} published {published} naive praos block(s)");
                }
                if let Some(rejected) = blocks_rejected.get(&id) {
                    info!("Pool {id} failed to publish {rejected} naive praos block(s) due to slot battles.");
                }
            }
        });

        info_span!("leios").in_scope(|| {
            let txs_which_reached_ib: Vec<_> = txs
                .values()
                .filter(|tx| tx.included_in_ib.is_some())
                .collect();
            let txs_per_ib = compute_stats(txs_in_ib.into_values());
            let bytes_per_ib = compute_stats(bytes_in_ib.into_values());
            let ibs_per_tx = compute_stats(ibs_containing_tx.into_values());
            let times_to_reach_ibs = compute_stats(txs_which_reached_ib.iter().map(|tx| {
                let duration = tx.included_in_ib.unwrap() - tx.generated;
                duration.as_secs_f64()
            }));
            let ibs_received = compute_stats(
                self.node_ids
                    .iter()
                    .map(|id| seen_ibs.get(id).copied().unwrap_or_default()),
            );
            info!(
                "{generated_ibs} IB(s) were generated, and {empty_ibs} IB(s) were skipped because they were empty; on average there were {:.3} non-empty IB(s) per slot.",
                generated_ibs as f64 / total_slots as f64
            );
            info!(
                "{} out of {} transaction(s) were included in at least one IB.",
                txs_which_reached_ib.len(),
                txs.len(),
            );
            let avg_age = pending_txs.iter().map(|id| {
                let tx = txs.get(&id).unwrap();
                (last_timestamp - tx.generated).as_secs_f64()
            });
            let avg_age_stats = compute_stats(avg_age);
            info!(
                "The average age of the pending transactions is {:.3}s (stddev {:.3}).",
                avg_age_stats.mean, avg_age_stats.std_dev,
            );
            info!(
                "Each transaction was included in an average of {:.3} IB(s) (stddev {:.3}).",
                ibs_per_tx.mean, ibs_per_tx.std_dev,
            );
            info!(
                "Each IB contained an average of {:.3} transaction(s) (stddev {:.3}) and an average of {} (stddev {:.3}).",
                txs_per_ib.mean, txs_per_ib.std_dev,
                pretty_bytes(bytes_per_ib.mean.trunc() as u64, pbo), bytes_per_ib.std_dev,
            );
            info!(
                "Each transaction took an average of {:.3}s (stddev {:.3}) to be included in an IB.",
                times_to_reach_ibs.mean, times_to_reach_ibs.std_dev,
            );
            info!(
                "Each node received an average of {:.3} IB(s) (stddev {:.3}).",
                ibs_received.mean, ibs_received.std_dev,
            );
        });
        Ok(())
    }
}

struct Transaction {
    bytes: u64,
    generated: Timestamp,
    included_in_ib: Option<Timestamp>,
}

struct Stats {
    mean: f64,
    std_dev: f64,
}

fn compute_stats<Iter: IntoIterator<Item = f64>>(data: Iter) -> Stats {
    let v: Variance = data.into_iter().collect();
    Stats {
        mean: v.mean(),
        std_dev: v.population_variance().sqrt(),
    }
}

fn should_log_event(event: &Event) -> bool {
    if matches!(event, Event::EmptyInputBlockNotGenerated { .. }) {
        return false;
    }
    true
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
