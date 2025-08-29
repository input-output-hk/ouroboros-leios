use std::{collections::HashMap, sync::Arc};

use rand::{RngCore, SeedableRng};
use rand_chacha::ChaChaRng;
use tokio::sync::mpsc;

use crate::{
    clock::{Clock, MockClockCoordinator, Timestamp},
    config::{NodeId, RawLinkInfo, RawNode, RawTopology, SimConfiguration, TransactionConfig},
    events::{Event, EventTracker},
    model::{LinearEndorserBlock, LinearRankingBlock, Transaction},
    sim::{
        EventResult, NodeImpl,
        linear_leios::{CpuTask, LinearLeiosNode, Message},
        lottery::{LotteryKind, MockLotteryResults},
    },
};

fn new_sim_config(topology: RawTopology) -> Arc<SimConfiguration> {
    let mut params: crate::config::RawParameters =
        serde_yaml::from_slice(include_bytes!("../../../../parameters/config.default.yaml"))
            .unwrap();
    params.leios_variant = crate::config::LeiosVariant::LinearWithTxReferences;
    // every transaction fills up exactly half of an RB
    let tx_size = params.rb_body_max_size_bytes / 2;
    params.tx_size_bytes_distribution = crate::config::DistributionConfig::Constant {
        value: tx_size as f64,
    };
    params.tx_max_size_bytes = tx_size;
    let topology = topology.into();
    Arc::new(SimConfiguration::build(params, topology).unwrap())
}

fn new_sim(
    sim_config: Arc<SimConfiguration>,
    event_tx: mpsc::UnboundedSender<(Event, Timestamp)>,
    clock: Clock,
) -> (
    HashMap<NodeId, LinearLeiosNode>,
    HashMap<NodeId, Arc<MockLotteryResults>>,
) {
    let tracker = EventTracker::new(event_tx, clock.clone(), &sim_config.nodes);
    let mut rng = ChaChaRng::seed_from_u64(sim_config.seed);
    let mut lottery = HashMap::new();
    let nodes = sim_config
        .nodes
        .iter()
        .map(|config| {
            let rng = ChaChaRng::seed_from_u64(rng.next_u64());
            let mut node = LinearLeiosNode::new(
                config,
                sim_config.clone(),
                tracker.clone(),
                rng,
                clock.clone(),
            );
            let lottery_results = Arc::new(MockLotteryResults::default());
            node.mock_lottery(lottery_results.clone());
            lottery.insert(config.id, lottery_results);
            (config.id, node)
        })
        .collect();
    (nodes, lottery)
}

fn new_topology(nodes: Vec<(&'static str, RawNode)>) -> RawTopology {
    RawTopology {
        nodes: nodes
            .into_iter()
            .map(|(name, node)| (name.to_string(), node))
            .collect(),
    }
}
fn new_node(stake: Option<u64>, producers: Vec<&'static str>) -> RawNode {
    RawNode {
        stake,
        location: crate::config::RawNodeLocation::Cluster {
            cluster: "all".into(),
        },
        cpu_core_count: Some(4),
        tx_conflict_fraction: None,
        tx_generation_weight: None,
        producers: producers
            .iter()
            .map(|n| {
                (
                    n.to_string(),
                    RawLinkInfo {
                        latency_ms: 0.0,
                        bandwidth_bytes_per_second: None,
                    },
                )
            })
            .collect(),
        adversarial: None,
        behaviours: vec![],
    }
}

struct TestDriver {
    sim_config: Arc<SimConfiguration>,
    rng: ChaChaRng,
    slot: u64,
    time: MockClockCoordinator,
    nodes: HashMap<NodeId, LinearLeiosNode>,
    lottery: HashMap<NodeId, Arc<MockLotteryResults>>,
    queued: HashMap<NodeId, EventResult<LinearLeiosNode>>,
}

impl TestDriver {
    fn new(topology: RawTopology) -> Self {
        let sim_config = new_sim_config(topology);
        let rng = ChaChaRng::seed_from_u64(sim_config.seed);
        let slot = 0;
        let time = MockClockCoordinator::new();
        let (event_tx, _event_rx) = mpsc::unbounded_channel();
        let (nodes, lottery) = new_sim(sim_config.clone(), event_tx, time.clock());
        Self {
            sim_config,
            rng,
            slot,
            time,
            nodes,
            lottery,
            queued: HashMap::new(),
        }
    }

    pub fn id_for(&self, name: &str) -> NodeId {
        self.sim_config
            .nodes
            .iter()
            .find_map(|n| if n.name == name { Some(n.id) } else { None })
            .unwrap()
    }

    pub fn produce_tx(&mut self, node_id: NodeId, conflict: bool) -> Arc<Transaction> {
        let TransactionConfig::Real(tx_config) = &self.sim_config.transactions else {
            panic!("unexpected TX config")
        };
        let tx = Arc::new(tx_config.new_tx(&mut self.rng, Some(if conflict { 1.0 } else { 0.0 })));
        let node = self.nodes.get_mut(&node_id).unwrap();
        let events = node.handle_new_tx(tx.clone());
        self.queued.entry(node_id).or_default().merge(events);
        tx
    }

    pub fn win_next_rb_lottery(&mut self, node_id: NodeId, result: u64) {
        self.lottery
            .get(&node_id)
            .unwrap()
            .configure_win(LotteryKind::GenerateRB, result);
    }

    pub fn next_slot(&mut self) {
        self.slot += 1;
        self.time.advance_time(Timestamp::from_secs(self.slot));
        for (node_id, node) in self.nodes.iter_mut() {
            let events = node.handle_new_slot(self.slot);
            self.queued.entry(*node_id).or_default().merge(events);
        }
    }

    pub fn expect_tx_sent(&mut self, from: NodeId, to: NodeId, tx: Arc<Transaction>) {
        self.expect_message(from, to, Message::AnnounceTx(tx.id));
        self.expect_message(to, from, Message::RequestTx(tx.id));
        self.expect_message(from, to, Message::Tx(tx.clone()));
        self.expect_cpu_task(to, CpuTask::TransactionValidated(from, tx));
    }

    pub fn expect_tx_not_sent(&mut self, from: NodeId, to: NodeId, tx: Arc<Transaction>) {
        self.expect_no_message(from, to, Message::AnnounceTx(tx.id));
    }

    pub fn expect_rb_and_eb_sent(
        &mut self,
        from: NodeId,
        to: NodeId,
        rb: Arc<LinearRankingBlock>,
        eb: Option<Arc<LinearEndorserBlock>>,
    ) {
        self.expect_message(from, to, Message::AnnounceRBHeader(rb.header.id));
        self.expect_message(to, from, Message::RequestRBHeader(rb.header.id));
        self.expect_message(
            from,
            to,
            Message::RBHeader(rb.header.clone(), true, eb.is_some()),
        );
        self.expect_cpu_task(
            to,
            CpuTask::RBHeaderValidated(from, rb.header.clone(), true, eb.is_some()),
        );
        self.expect_message(to, from, Message::RequestRB(rb.header.id));
        self.expect_message(from, to, Message::RB(rb.clone()));
        self.expect_cpu_task(to, CpuTask::RBBlockValidated(rb));
        if let Some(eb) = eb {
            self.expect_message(to, from, Message::RequestEB(eb.id()));
            self.expect_message(from, to, Message::EB(eb.clone()));
            self.expect_cpu_task(to, CpuTask::EBHeaderValidated(from, eb));
        }
    }

    pub fn expect_eb_validated(&mut self, node: NodeId, eb: Arc<LinearEndorserBlock>) {
        self.expect_cpu_task(node, CpuTask::EBBlockValidated(eb, self.time.now()));
    }

    pub fn expect_message(
        &mut self,
        from: NodeId,
        to: NodeId,
        message: <LinearLeiosNode as NodeImpl>::Message,
    ) {
        let queued = self.queued.entry(from).or_default();
        let mut found = false;
        queued.messages.retain(|(t, msg)| {
            if t == &to && msg == &message {
                found = true;
                false
            } else {
                true
            }
        });
        assert!(
            found,
            "message {message:?} was not sent from {from} to {to}\npending messages: {:?}",
            queued
                .messages
                .iter()
                .filter(|(t, _)| t == &to)
                .collect::<Vec<_>>(),
        );
        let events = self
            .nodes
            .get_mut(&to)
            .unwrap()
            .handle_message(from, message);
        self.queued.entry(to).or_default().merge(events);
    }

    pub fn expect_no_message(
        &mut self,
        from: NodeId,
        to: NodeId,
        message: <LinearLeiosNode as NodeImpl>::Message,
    ) {
        let Some(queued) = self.queued.get(&from) else {
            return;
        };
        for (t, m) in &queued.messages {
            assert_ne!((t, m), (&to, &message));
        }
    }

    pub fn expect_cpu_task(&mut self, node: NodeId, task: <LinearLeiosNode as NodeImpl>::Task) {
        self.expect_cpu_task_matching(node, |t| if *t == task { Some(t.clone()) } else { None });
    }

    pub fn expect_cpu_task_matching<T, M>(&mut self, node: NodeId, matcher: M) -> T
    where
        M: Fn(&<LinearLeiosNode as NodeImpl>::Task) -> Option<T>,
    {
        let queued = self.queued.entry(node).or_default();
        let mut result = None;
        let mut new_queued = EventResult::default();
        queued.tasks.retain(|t| {
            if result.is_some() {
                return true;
            }
            result = matcher(t);
            if result.is_some() {
                new_queued = self
                    .nodes
                    .get_mut(&node)
                    .unwrap()
                    .handle_cpu_task(t.clone());
            }
            result.is_none()
        });
        queued.merge(new_queued);
        result.expect("no CPU tasks matching filter")
    }
}

fn is_new_rb_task(
    task: &CpuTask,
) -> Option<(Arc<LinearRankingBlock>, Option<Arc<LinearEndorserBlock>>)> {
    match task {
        CpuTask::RBBlockGenerated(rb, eb) => Some((
            Arc::new(rb.clone()),
            eb.as_ref().map(|(eb, _)| Arc::new(eb.clone())),
        )),
        _ => None,
    }
}

#[test]
fn should_propagate_transactions() {
    let topology = new_topology(vec![
        ("node-1", new_node(Some(1000), vec!["node-2"])),
        ("node-2", new_node(Some(1000), vec!["node-1"])),
    ]);
    let mut sim = TestDriver::new(topology);
    let node1 = sim.id_for("node-1");
    let node2 = sim.id_for("node-2");

    // Node 1 produces a transaction, node 2 should request it
    let tx1 = sim.produce_tx(node1, false);
    sim.expect_tx_sent(node1, node2, tx1.clone());

    // Node 2 produces a transaction, node 1 should request it
    let tx2 = sim.produce_tx(node2, false);
    sim.expect_tx_sent(node2, node1, tx2.clone());

    // When node 1 produces an RB, it should include both TXs
    sim.win_next_rb_lottery(node1, 0);
    sim.next_slot();
    let (new_rb, new_eb) = sim.expect_cpu_task_matching(node1, is_new_rb_task);
    assert_eq!(new_rb.transactions, vec![tx1, tx2]);
    assert_eq!(new_eb, None);
}

#[test]
fn should_not_propagate_conflicting_transactions() {
    let topology = new_topology(vec![
        ("node-1", new_node(Some(1000), vec!["node-2"])),
        ("node-2", new_node(Some(1000), vec!["node-1"])),
    ]);
    let mut sim = TestDriver::new(topology);
    let node1 = sim.id_for("node-1");
    let node2 = sim.id_for("node-2");

    // Node 1 and 2 produce conflicting transactions
    let tx1 = sim.produce_tx(node1, false);
    let tx2 = sim.produce_tx(node2, true);

    // Each node should send its TX to the other node,
    sim.expect_tx_sent(node1, node2, tx1.clone());
    sim.expect_tx_sent(node2, node1, tx2.clone());

    // When node 1 produces an RB, it should include only its own TX
    sim.win_next_rb_lottery(node1, 0);
    sim.next_slot();
    let (new_rb, new_eb) = sim.expect_cpu_task_matching(node1, is_new_rb_task);
    assert_eq!(new_rb.transactions, vec![tx1]);
    assert_eq!(new_eb, None);
}

#[test]
fn should_repropagate_conflicting_transactions_from_eb() {
    let topology = new_topology(vec![
        ("node-1", new_node(Some(1000), vec!["node-2"])),
        ("node-2", new_node(Some(1000), vec!["node-1", "node-3"])),
        ("node-3", new_node(Some(1000), vec!["node-2"])),
    ]);
    let mut sim = TestDriver::new(topology);
    let node1 = sim.id_for("node-1");
    let node2 = sim.id_for("node-2");
    let node3 = sim.id_for("node-3");

    // Node 1 produces 3 transactions
    let tx1_1 = sim.produce_tx(node1, false);
    let tx1_2 = sim.produce_tx(node1, false);
    let tx1_3 = sim.produce_tx(node1, false);

    // Node 2 produces a transaction which conflicts with Node 1's final transaction
    let tx2 = sim.produce_tx(node2, true);
    // Node 2 sends its transactions to nodes 1 and 3
    sim.expect_tx_sent(node2, node1, tx2.clone());
    sim.expect_tx_sent(node2, node3, tx2.clone());

    // Node 1 sends all of its transactions to node 2
    sim.expect_tx_sent(node1, node2, tx1_1.clone());
    sim.expect_tx_sent(node1, node2, tx1_2.clone());
    sim.expect_tx_sent(node1, node2, tx1_3.clone());

    // Node 2 sends the first two transactions to node 3, but not the conflicting third
    sim.expect_tx_sent(node2, node3, tx1_1.clone());
    sim.expect_tx_sent(node2, node3, tx1_2.clone());
    sim.expect_tx_not_sent(node2, node3, tx1_3.clone());

    // Now, Node 1 produces an RB (with an EB, because there are enough transactions)
    sim.win_next_rb_lottery(node1, 0);
    sim.next_slot();
    let (rb, eb) = sim.expect_cpu_task_matching(node1, is_new_rb_task);
    let eb = eb.expect("node did not produce EB");
    assert_eq!(rb.transactions, vec![tx1_1, tx1_2]);
    assert_eq!(eb.txs, vec![tx1_3.clone()]);

    // That RB and EB propagate from node 1 to node 2
    sim.expect_rb_and_eb_sent(node1, node2, rb.clone(), Some(eb.clone()));
    // Node 2 fully validates the EB, because node 1 has all TXs
    sim.expect_eb_validated(node2, eb.clone());
    // And Node 2 propagates it to Node 3
    sim.expect_rb_and_eb_sent(node2, node3, rb.clone(), Some(eb.clone()));

    // and NOW Node 2 will tell Node 3 about the EB's conflicting TX
    sim.expect_tx_sent(node2, node3, tx1_3);
    sim.expect_eb_validated(node3, eb);
}
