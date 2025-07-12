use std::collections::{BTreeMap, BTreeSet, VecDeque};

use sim_core::{
    clock::Timestamp,
    config::SimConfiguration,
    events::{BlockRef, Event},
    model::{TransactionId, TransactionLostReason},
};
use tokio::sync::mpsc;

use super::{EndorserBlockId, InputBlockId};

/// Emits additional events when it is no longer possible for a transaction to reach the chain.
pub struct LivenessMonitor {
    events_source: mpsc::UnboundedReceiver<(Event, Timestamp)>,
    queue: VecDeque<(Event, Timestamp)>,
    txs: BTreeMap<TransactionId, MonitoredTX>,
    ibs: BTreeMap<InputBlockId, MonitoredIB>,
    ebs: BTreeMap<EndorserBlockId, MonitoredEB>,
    stage_length: u64,
    vote_threshold: u64,
}

impl LivenessMonitor {
    pub fn new(
        config: &SimConfiguration,
        events_source: mpsc::UnboundedReceiver<(Event, Timestamp)>,
    ) -> Self {
        Self {
            events_source,
            queue: VecDeque::new(),
            txs: BTreeMap::new(),
            ibs: BTreeMap::new(),
            ebs: BTreeMap::new(),
            stage_length: config.stage_length,
            vote_threshold: config.vote_threshold,
        }
    }

    pub async fn recv(&mut self) -> Option<(Event, Timestamp)> {
        if let Some(next) = self.queue.pop_front() {
            return Some(next);
        }
        let (event, time) = self.events_source.recv().await?;
        match &event {
            Event::TXGenerated { id, .. } => {
                self.txs.insert(*id, MonitoredTX::new());
            }
            Event::IBGenerated {
                id, transactions, ..
            } => {
                for tx_id in transactions {
                    if let Some(tx) = self.txs.get_mut(tx_id) {
                        tx.ibs.insert(id.clone());
                        tx.last_ib_pipeline = std::cmp::max(tx.last_ib_pipeline, Some(id.pipeline));
                    }
                }
                self.ibs
                    .insert(id.clone(), MonitoredIB::new(transactions.clone()));
            }
            Event::EBGenerated {
                id,
                transactions,
                input_blocks,
                endorser_blocks,
                ..
            } => {
                for BlockRef { id: tx_id } in transactions {
                    if let Some(tx) = self.txs.get_mut(tx_id) {
                        tx.ebs.insert(id.clone());
                        tx.last_eb_pipeline = std::cmp::max(tx.last_eb_pipeline, Some(id.pipeline));
                    }
                }
                for BlockRef { id: ib_id } in input_blocks {
                    if let Some(ib) = self.ibs.get(ib_id) {
                        for tx_id in &ib.txs {
                            if let Some(tx) = self.txs.get_mut(tx_id) {
                                tx.ebs.insert(id.clone());
                                tx.last_eb_pipeline =
                                    std::cmp::max(tx.last_eb_pipeline, Some(id.pipeline));
                            }
                        }
                    }
                }
                self.ebs.insert(
                    id.clone(),
                    MonitoredEB::new(
                        transactions.iter().map(|tx| tx.id).collect(),
                        input_blocks.iter().map(|ib| ib.id.clone()).collect(),
                        endorser_blocks.iter().map(|eb| eb.id.clone()).collect(),
                    ),
                );
            }
            Event::VTBundleGenerated { votes, .. } => {
                for (eb_id, count) in &votes.0 {
                    let Some(eb) = self.ebs.get_mut(eb_id) else {
                        continue;
                    };
                    eb.votes += *count as u64;
                    if eb.votes >= self.vote_threshold {
                        for ib_id in &eb.ibs {
                            if let Some(ib) = self.ibs.get_mut(ib_id) {
                                for tx_id in &ib.txs {
                                    if let Some(tx) = self.txs.get_mut(tx_id) {
                                        tx.certified_ebs.insert(eb_id.clone());
                                    }
                                }
                            }
                        }
                        for tx_id in &eb.txs {
                            if let Some(tx) = self.txs.get_mut(tx_id) {
                                tx.certified_ebs.insert(eb_id.clone());
                            }
                        }
                    }
                }
            }
            Event::RBGenerated {
                endorsement,
                transactions,
                ..
            } => {
                for tx in transactions {
                    self.txs.remove(tx);
                }
                if let Some(endorsement) = endorsement {
                    let mut eb_queue = vec![endorsement.eb.id.clone()];
                    while let Some(eb_id) = eb_queue.pop() {
                        let Some(eb) = self.ebs.remove(&eb_id) else {
                            continue;
                        };
                        self.txs.retain(|_, tx| !tx.ebs.contains(&eb_id));
                        for ib_id in &eb.ibs {
                            self.ibs.remove(ib_id);
                        }
                        eb_queue.extend(eb.ebs);
                    }
                }
            }
            Event::GlobalSlot { slot } => {
                if slot % self.stage_length == 0 {
                    let pipeline = slot / self.stage_length;
                    self.handle_new_pipeline(pipeline, time);
                }
            }
            _ => {}
        }
        Some((event, time))
    }

    fn handle_new_pipeline(&mut self, pipeline: u64, time: Timestamp) {
        self.txs.retain(|id, tx| {
            if tx.ebs.is_empty()
                && tx
                    .last_ib_pipeline
                    .is_some_and(|ib_pipeline| ib_pipeline + 4 < pipeline)
            {
                // this transaction was only in IBs which never reached any EBs.
                self.queue.push_back((
                    Event::TXLost {
                        id: *id,
                        reason: TransactionLostReason::IBExpired,
                    },
                    time,
                ));
                return false;
            }

            if tx.certified_ebs.is_empty()
                && tx
                    .last_eb_pipeline
                    .is_some_and(|eb_pipeline| eb_pipeline + 1 < pipeline)
            {
                // this transaction was only in EBs which were never certified
                self.queue.push_back((
                    Event::TXLost {
                        id: *id,
                        reason: TransactionLostReason::EBExpired,
                    },
                    time,
                ));
                return false;
            }

            true
        });
    }
}

struct MonitoredTX {
    last_ib_pipeline: Option<u64>,
    ibs: BTreeSet<InputBlockId>,
    last_eb_pipeline: Option<u64>,
    ebs: BTreeSet<EndorserBlockId>,
    certified_ebs: BTreeSet<EndorserBlockId>,
}
impl MonitoredTX {
    fn new() -> Self {
        Self {
            last_ib_pipeline: None,
            ibs: BTreeSet::new(),
            last_eb_pipeline: None,
            ebs: BTreeSet::new(),
            certified_ebs: BTreeSet::new(),
        }
    }
}

struct MonitoredIB {
    txs: Vec<TransactionId>,
}
impl MonitoredIB {
    fn new(txs: Vec<TransactionId>) -> Self {
        Self { txs }
    }
}

struct MonitoredEB {
    txs: Vec<TransactionId>,
    ibs: Vec<InputBlockId>,
    ebs: Vec<EndorserBlockId>,
    votes: u64,
}
impl MonitoredEB {
    fn new(txs: Vec<TransactionId>, ibs: Vec<InputBlockId>, ebs: Vec<EndorserBlockId>) -> Self {
        Self {
            txs,
            ibs,
            ebs,
            votes: 0,
        }
    }
}
