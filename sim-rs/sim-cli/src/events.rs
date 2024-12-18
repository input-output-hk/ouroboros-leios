use std::{
    collections::{BTreeMap, BTreeSet},
    path::PathBuf,
};

use anyhow::Result;
use average::Variance;
use itertools::Itertools as _;
use pretty_bytes_rust::{pretty_bytes, PrettyBytesOptions};
use serde::Serialize;
use sim_core::{
    clock::Timestamp,
    config::{NodeId, SimConfiguration},
    events::Event,
    model::{EndorserBlockId, InputBlockId, TransactionId, VoteBundleId},
};
use tokio::{
    fs::{self, File},
    io::{AsyncWriteExt as _, BufWriter},
    sync::mpsc,
};
use tracing::{info, info_span};

#[derive(Clone, Serialize)]
struct OutputEvent {
    time: Timestamp,
    message: Event,
}

#[derive(clap::ValueEnum, Clone, Copy)]
pub enum OutputFormat {
    EventStream,
    SlotStream,
}

pub struct EventMonitor {
    node_ids: Vec<NodeId>,
    pool_ids: Vec<NodeId>,
    stage_length: u64,
    maximum_ib_age: u64,
    events_source: mpsc::UnboundedReceiver<(Event, Timestamp)>,
    output_path: Option<PathBuf>,
    output_format: OutputFormat,
}

impl EventMonitor {
    pub fn new(
        config: &SimConfiguration,
        events_source: mpsc::UnboundedReceiver<(Event, Timestamp)>,
        output_path: Option<PathBuf>,
        output_format: Option<OutputFormat>,
    ) -> Self {
        let node_ids = config.nodes.iter().map(|p| p.id).collect();
        let pool_ids = config
            .nodes
            .iter()
            .filter_map(|p| if p.stake > 0 { Some(p.id) } else { None })
            .collect();
        let stage_length = config.stage_length;
        let maximum_ib_age = stage_length * (config.deliver_stage_count + 1);
        Self {
            node_ids,
            pool_ids,
            stage_length,
            maximum_ib_age,
            events_source,
            output_path,
            output_format: output_format.unwrap_or(OutputFormat::EventStream),
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
        let mut ibs_in_eb: BTreeMap<EndorserBlockId, f64> = BTreeMap::new();
        let mut ibs_containing_tx: BTreeMap<TransactionId, f64> = BTreeMap::new();
        let mut ebs_containing_ib: BTreeMap<InputBlockId, f64> = BTreeMap::new();
        let mut pending_ibs: BTreeSet<InputBlockId> = BTreeSet::new();
        let mut votes_per_bundle: BTreeMap<VoteBundleId, f64> = BTreeMap::new();
        let mut votes_per_pool: BTreeMap<NodeId, f64> =
            self.pool_ids.into_iter().map(|id| (id, 0.0)).collect();
        let mut eb_votes: BTreeMap<EndorserBlockId, f64> = BTreeMap::new();
        let mut ib_txs: BTreeMap<InputBlockId, Vec<TransactionId>> = BTreeMap::new();
        let mut eb_ibs: BTreeMap<EndorserBlockId, Vec<InputBlockId>> = BTreeMap::new();

        let mut last_timestamp = Timestamp::zero();
        let mut total_slots = 0u64;
        let mut praos_txs = 0u64;
        let mut published_bytes = 0u64;
        let mut generated_ibs = 0u64;
        let mut empty_ibs = 0u64;
        let mut expired_ibs = 0u64;
        let mut generated_ebs = 0u64;
        let mut total_votes = 0u64;
        let mut leios_blocks_with_endorsements = 0u64;
        let mut leios_txs = 0u64;
        let mut tx_messages = MessageStats::default();
        let mut ib_messages = MessageStats::default();
        let mut eb_messages = MessageStats::default();
        let mut vote_messages = MessageStats::default();

        // Pretty print options for bytes
        let pbo = Some(PrettyBytesOptions {
            use_1024_instead_of_1000: Some(false),
            number_of_decimal: Some(2),
            remove_zero_decimal: Some(true),
        });

        if let Some(path) = &self.output_path {
            if let Some(parent) = path.parent() {
                fs::create_dir_all(parent).await?;
            }
        }

        let mut output = match self.output_path {
            Some(ref path) => {
                let file = File::create(path).await?;
                match self.output_format {
                    OutputFormat::EventStream => OutputTarget::EventStream(BufWriter::new(file)),
                    OutputFormat::SlotStream => OutputTarget::SlotStream {
                        file: BufWriter::new(file),
                        next: None,
                    },
                }
            }
            None => OutputTarget::None,
        };
        while let Some((event, time)) = self.events_source.recv().await {
            last_timestamp = time;
            let output_event = OutputEvent {
                time,
                message: event.clone(),
            };
            output.write(output_event).await?;
            match event {
                Event::Slot { number } => {
                    info!("Slot {number} has begun.");
                    total_slots = number + 1;
                    if number % self.stage_length == 0 {
                        let Some(oldest_live_stage) = number.checked_sub(self.maximum_ib_age)
                        else {
                            continue;
                        };
                        pending_ibs.retain(|ib| {
                            if ib.slot < oldest_live_stage {
                                expired_ibs += 1;
                                return false;
                            }
                            true
                        });
                    }
                }
                Event::TransactionGenerated { id, bytes, .. } => {
                    txs.insert(id, Transaction::new(bytes, time));
                    pending_txs.insert(id);
                }
                Event::TransactionSent { .. } => {
                    tx_messages.sent += 1;
                }
                Event::TransactionReceived { .. } => {
                    tx_messages.received += 1;
                }
                Event::PraosBlockGenerated {
                    slot,
                    producer,
                    vrf,
                    endorsement,
                    transactions,
                } => {
                    let mut all_txs = transactions;
                    info!(
                        "Pool {} produced a praos block in slot {slot} with {} tx(s).",
                        producer,
                        all_txs.len()
                    );
                    praos_txs += all_txs.len() as u64;
                    if let Some(endorsement) = endorsement {
                        leios_blocks_with_endorsements += 1;
                        let mut block_leios_txs: Vec<_> = eb_ibs
                            .get(&endorsement.eb)
                            .unwrap()
                            .iter()
                            .flat_map(|ib| ib_txs.get(ib).unwrap())
                            .copied()
                            .dedup()
                            .collect();
                        info!(
                            "This block had an additional {} leios tx(s).",
                            block_leios_txs.len()
                        );
                        leios_txs += block_leios_txs.len() as u64;
                        all_txs.append(&mut block_leios_txs);
                    }
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
                    for published_tx in all_txs {
                        let tx = txs.get_mut(&published_tx).unwrap();
                        if tx.included_in_block.is_none() {
                            tx.included_in_block = Some(time);
                        }
                        published_bytes += tx.bytes;
                        pending_txs.remove(&published_tx);
                    }
                }
                Event::PraosBlockSent { .. } => {}
                Event::PraosBlockReceived { .. } => {}
                Event::InputBlockGenerated {
                    header,
                    transactions,
                } => {
                    generated_ibs += 1;
                    if transactions.is_empty() {
                        empty_ibs += 1;
                    }
                    pending_ibs.insert(header.id);
                    ib_txs.insert(header.id, transactions.clone());
                    let mut ib_bytes = 0;
                    for tx_id in &transactions {
                        *txs_in_ib.entry(header.id).or_default() += 1.;
                        *ibs_containing_tx.entry(*tx_id).or_default() += 1.;
                        let tx = txs.get_mut(tx_id).unwrap();
                        ib_bytes += tx.bytes;
                        *bytes_in_ib.entry(header.id).or_default() += tx.bytes as f64;
                        if tx.included_in_ib.is_none() {
                            tx.included_in_ib = Some(time);
                        }
                    }
                    *seen_ibs.entry(header.id.producer).or_default() += 1.;
                    info!(
                        "Pool {} generated an IB with {} transaction(s) in slot {} ({}).",
                        header.id.producer,
                        transactions.len(),
                        header.id.slot,
                        pretty_bytes(ib_bytes, pbo.clone()),
                    )
                }
                Event::InputBlockSent { .. } => {
                    ib_messages.sent += 1;
                }
                Event::InputBlockReceived { recipient, .. } => {
                    ib_messages.received += 1;
                    *seen_ibs.entry(recipient).or_default() += 1.;
                }
                Event::EndorserBlockGenerated { id, input_blocks } => {
                    generated_ebs += 1;
                    eb_ibs.insert(id, input_blocks.clone());
                    for ib_id in &input_blocks {
                        *ibs_in_eb.entry(id).or_default() += 1.0;
                        *ebs_containing_ib.entry(*ib_id).or_default() += 1.0;
                        pending_ibs.remove(ib_id);
                        for tx_id in ib_txs.get(ib_id).unwrap() {
                            let tx = txs.get_mut(tx_id).unwrap();
                            if tx.included_in_eb.is_none() {
                                tx.included_in_eb = Some(time);
                            }
                        }
                    }
                    info!(
                        "Pool {} generated an EB with {} IBs(s) in slot {}.",
                        id.producer,
                        input_blocks.len(),
                        id.slot,
                    )
                }
                Event::EndorserBlockSent { .. } => {
                    eb_messages.sent += 1;
                }
                Event::EndorserBlockReceived { .. } => {
                    eb_messages.received += 1;
                }
                Event::VotesGenerated { id, ebs } => {
                    for eb in ebs {
                        total_votes += 1;
                        *votes_per_bundle.entry(id).or_default() += 1.0;
                        *eb_votes.entry(eb).or_default() += 1.0;
                        *votes_per_pool.entry(id.producer).or_default() += 1.0;
                    }
                }
                Event::NoVote { .. } => {}
                Event::VotesSent { .. } => {
                    vote_messages.sent += 1;
                }
                Event::VotesReceived { .. } => {
                    vote_messages.received += 1;
                }
            }
        }

        output.flush().await?;

        info_span!("praos").in_scope(|| {
            info!("{} transactions(s) were generated in total.", txs.len());
            info!("{} naive praos block(s) were published.", blocks.len());
            info!(
                "{} slot(s) had no naive praos blocks.",
                total_slots - blocks.len() as u64
            );
            info!("{} transaction(s) ({}) finalized in a naive praos block.", praos_txs + leios_txs, pretty_bytes(published_bytes, pbo.clone()));
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

            for id in &self.node_ids {
                if let Some(published) = blocks_published.get(id) {
                    info!("Pool {id} published {published} naive praos block(s)");
                }
                if let Some(rejected) = blocks_rejected.get(id) {
                    info!("Pool {id} failed to publish {rejected} naive praos block(s) due to slot battles.");
                }
            }
        });

        info_span!("leios").in_scope(|| {
            let times_to_reach_ib: Vec<_> = txs
                .values()
                .filter_map(|tx| {
                    let ib_time = tx.included_in_ib?;
                    Some(ib_time - tx.generated)
                })
                .collect();
            let times_to_reach_eb: Vec<_> = txs
                .values()
                .filter_map(|tx| {
                    let eb_time = tx.included_in_eb?;
                    Some(eb_time - tx.generated)
                })
                .collect();
            let times_to_reach_block: Vec<_> = txs
                .values()
                .filter_map(|tx| {
                    let block_time = tx.included_in_block?;
                    Some(block_time - tx.generated)
                })
                .collect();
            let empty_ebs = generated_ebs - ibs_in_eb.len() as u64;
            let ibs_which_reached_eb = ebs_containing_ib.len();
            let bundle_count = votes_per_bundle.len();
            let txs_per_ib = compute_stats(txs_in_ib.into_values());
            let bytes_per_ib = compute_stats(bytes_in_ib.into_values());
            let ibs_per_tx = compute_stats(ibs_containing_tx.into_values());
            let ibs_per_eb = compute_stats(ebs_containing_ib.into_values());
            let ebs_per_ib = compute_stats(ibs_in_eb.into_values());
            let ib_time_stats = compute_stats(times_to_reach_ib.iter().map(|t| t.as_secs_f64()));
            let eb_time_stats = compute_stats(times_to_reach_eb.iter().map(|t| t.as_secs_f64()));
            let block_time_stats = compute_stats(times_to_reach_block.iter().map(|t| t.as_secs_f64()));
            let ibs_received = compute_stats(
                self.node_ids
                    .iter()
                    .map(|id| seen_ibs.get(id).copied().unwrap_or_default()),
            );
            let votes_per_pool = compute_stats(votes_per_pool.into_values());
            let votes_per_eb = compute_stats(eb_votes.into_values());
            let votes_per_bundle = compute_stats(votes_per_bundle.into_values());

            info!(
                "{generated_ibs} IB(s) were generated, on average {:.3} IB(s) per slot.",
                generated_ibs as f64 / total_slots as f64
            );
            info!(
                "{} out of {} transaction(s) were included in at least one IB.",
                times_to_reach_ib.len(),
                txs.len(),
            );
            let avg_age = pending_txs.iter().map(|id| {
                let tx = txs.get(id).unwrap();
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
                "Each IB contained an average of {:.3} transaction(s) (stddev {:.3}) and an average of {} (stddev {:.3}). {} IB(s) were empty.",
                txs_per_ib.mean, txs_per_ib.std_dev,
                pretty_bytes(bytes_per_ib.mean.trunc() as u64, pbo.clone()), pretty_bytes(bytes_per_ib.std_dev.trunc() as u64, pbo),
                empty_ibs,
            );
            info!(
                "Each node received an average of {:.3} IB(s) (stddev {:.3}).",
                ibs_received.mean, ibs_received.std_dev,
            );
            info!(
                "{generated_ebs} EB(s) were generated; on average there were {:.3} EB(s) per slot.",
                generated_ebs as f64 / total_slots as f64
            );
            info!(
                "Each EB contained an average of {:.3} IB(s) (stddev {:.3}). {} EB(s) were empty.",
                ibs_per_eb.mean, ibs_per_eb.std_dev, empty_ebs
            );
            info!(
                "Each IB was included in an average of {:.3} EB(s) (stddev {:.3}).",
                ebs_per_ib.mean, ebs_per_ib.std_dev,
            );
            info!(
                "{} out of {} IBs were included in at least one EB.",
                ibs_which_reached_eb, generated_ibs,
            );
            info!(
                "{} out of {} IBs expired before they reached an EB.",
                expired_ibs, generated_ibs,
            );
            info!(
                "{} out of {} transaction(s) were included in at least one EB.",
                times_to_reach_eb.len(), txs.len(),
            );
            info!("{} total votes were generated.", total_votes);
            info!("Each stake pool produced an average of {:.3} vote(s) (stddev {:.3}).",
                votes_per_pool.mean, votes_per_pool.std_dev);
            info!("Each EB received an average of {:.3} vote(s) (stddev {:.3}).",
                votes_per_eb.mean, votes_per_eb.std_dev);
            info!("There were {bundle_count} bundle(s) of votes. Each bundle contained {:.3} vote(s) (stddev {:.3}).",
                votes_per_bundle.mean, votes_per_bundle.std_dev);
            info!("{} L1 block(s) had a Leios endorsement.", leios_blocks_with_endorsements);
            info!("{} tx(s) were referenced by a Leios endorsement.", leios_txs);
            info!("{} tx(s) were included directly in a Praos block.", praos_txs);
            info!(
                "Each transaction took an average of {:.3}s (stddev {:.3}) to be included in an IB.",
                ib_time_stats.mean, ib_time_stats.std_dev,
            );
            info!(
                "Each transaction took an average of {:.3}s (stddev {:.3}) to be included in an EB.",
                eb_time_stats.mean, eb_time_stats.std_dev,
            );
            info!(
                "Each transaction took an average of {:.3}s (stddev {:.3}) to be included in a block.",
                block_time_stats.mean, block_time_stats.std_dev,
            );
        });

        info_span!("network").in_scope(|| {
            tx_messages.display("TX");
            ib_messages.display("IB");
            eb_messages.display("EB");
            vote_messages.display("Vote");
        });

        Ok(())
    }
}

struct Transaction {
    bytes: u64,
    generated: Timestamp,
    included_in_ib: Option<Timestamp>,
    included_in_eb: Option<Timestamp>,
    included_in_block: Option<Timestamp>,
}
impl Transaction {
    fn new(bytes: u64, generated: Timestamp) -> Self {
        Self {
            bytes,
            generated,
            included_in_ib: None,
            included_in_eb: None,
            included_in_block: None,
        }
    }
}

#[derive(Default)]
struct MessageStats {
    sent: u64,
    received: u64,
}
impl MessageStats {
    fn display(&self, name: &str) {
        let percent_received = self.received as f64 / self.sent as f64 * 100.0;
        info!(
            "{} {} message(s) were sent. {} of them were received ({:.3}%).",
            self.sent, name, self.received, percent_received
        );
    }
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

enum OutputTarget {
    EventStream(BufWriter<File>),
    SlotStream {
        file: BufWriter<File>,
        next: Option<SlotEvents>,
    },
    None,
}

#[derive(Serialize)]
struct SlotEvents {
    slot: u64,
    start_time: Timestamp,
    events: Vec<OutputEvent>,
}
impl OutputTarget {
    async fn write(&mut self, event: OutputEvent) -> Result<()> {
        match self {
            Self::EventStream(file) => {
                Self::write_line(file, event).await?;
            }
            Self::SlotStream { file, next } => {
                if let Event::Slot { number } = &event.message {
                    if let Some(slot) = next.take() {
                        Self::write_line(file, slot).await?;
                    }
                    *next = Some(SlotEvents {
                        slot: *number,
                        start_time: event.time,
                        events: vec![],
                    });
                } else if let Some(slot) = next.as_mut() {
                    slot.events.push(event);
                }
            }
            Self::None => {}
        }
        Ok(())
    }

    async fn write_line<T: Serialize>(file: &mut BufWriter<File>, event: T) -> Result<()> {
        let mut string = serde_json::to_string(&event)?;
        string.push('\n');
        file.write_all(string.as_bytes()).await?;
        Ok(())
    }

    async fn flush(self) -> Result<()> {
        match self {
            Self::EventStream(mut file) => {
                file.flush().await?;
            }
            Self::SlotStream { mut file, mut next } => {
                if let Some(slot) = next.take() {
                    Self::write_line(&mut file, slot).await?;
                }
                file.flush().await?;
            }
            Self::None => {}
        };
        Ok(())
    }
}
