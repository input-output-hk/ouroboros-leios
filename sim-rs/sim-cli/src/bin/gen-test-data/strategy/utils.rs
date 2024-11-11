use std::{
    collections::{BTreeMap, BTreeSet},
    time::Duration,
};

use sim_core::config::RawLinkConfig;

#[derive(Default)]
pub struct LinkTracker {
    pub connections: BTreeMap<usize, BTreeSet<usize>>,
    pub links: Vec<RawLinkConfig>,
}

impl LinkTracker {
    pub fn new() -> Self {
        Self::default()
    }
    pub fn add(&mut self, from: usize, to: usize, latency: Option<Duration>) {
        if to < from {
            self.add(to, from, latency);
            return;
        }
        self.links.push(RawLinkConfig {
            nodes: (from, to),
            latency_ms: latency.map(|l| l.as_millis() as u64),
        });
        self.connections.entry(from).or_default().insert(to);
        self.connections.entry(to).or_default().insert(from);
    }
}
