use std::{sync::Arc, time::Duration};

use rand_chacha::ChaChaRng;
use rand_chacha::rand_core::SeedableRng;
use tokio::sync::mpsc;
use tokio_util::sync::CancellationToken;

use crate::{
    clock::{Clock, Timestamp},
    config::{
        CpuTimeConfig, NodeConfiguration, NodeId, RawLinkInfo, RawNode, RawNodeLocation,
        RawTopology, SimConfiguration,
    },
    events::{Event, EventTracker},
    model::Transaction,
    sim::{EventResult, MiniProtocol, NodeImpl, SimCpuTask, SimMessage},
};

// ---------------------------------------------------------------------------
// TestNode types
// ---------------------------------------------------------------------------

#[derive(Clone, Debug)]
enum TestMessage {
    Ping { from: NodeId, slot: u64 },
    Pong { from: NodeId, slot: u64 },
}

impl SimMessage for TestMessage {
    fn protocol(&self) -> MiniProtocol {
        MiniProtocol::Block
    }
    fn bytes_size(&self) -> u64 {
        100
    }
}

#[derive(Debug)]
enum TestCpuTask {
    ValidateTx,
}

impl SimCpuTask for TestCpuTask {
    fn name(&self) -> String {
        "validate_tx".into()
    }
    fn extra(&self) -> String {
        String::new()
    }
    fn times(&self, _config: &CpuTimeConfig) -> Vec<Duration> {
        vec![Duration::from_millis(10)]
    }
}

#[derive(Debug)]
enum TestTimedEvent {
    SendPong { to: NodeId, slot: u64 },
}

// ---------------------------------------------------------------------------
// TestNode implementation
// ---------------------------------------------------------------------------

struct TestNode {
    id: NodeId,
    peers: Vec<NodeId>,
    clock: Clock,
    tracker: EventTracker,
}

impl NodeImpl for TestNode {
    type Message = TestMessage;
    type Task = TestCpuTask;
    type TimedEvent = TestTimedEvent;
    type CustomEvent = ();

    fn new(
        config: &NodeConfiguration,
        sim_config: Arc<SimConfiguration>,
        tracker: EventTracker,
        _rng: ChaChaRng,
        clock: Clock,
    ) -> Self {
        let peers: Vec<NodeId> = sim_config
            .links
            .iter()
            .filter_map(|l| {
                if l.nodes.0 == config.id {
                    Some(l.nodes.1)
                } else if l.nodes.1 == config.id {
                    Some(l.nodes.0)
                } else {
                    None
                }
            })
            .collect();
        TestNode {
            id: config.id,
            peers,
            clock,
            tracker,
        }
    }

    fn handle_new_slot(&mut self, slot: u64) -> EventResult<Self> {
        self.tracker
            .track_test_event(self.id, "slot", &format!("{slot}"));
        let mut result = EventResult::default();
        for &peer in &self.peers {
            result.send_to(
                peer,
                TestMessage::Ping {
                    from: self.id,
                    slot,
                },
            );
        }
        result
    }

    fn handle_new_tx(&mut self, _tx: Arc<Transaction>) -> EventResult<Self> {
        self.tracker.track_test_event(self.id, "tx_received", "");
        let mut result = EventResult::default();
        result.schedule_cpu_task(TestCpuTask::ValidateTx);
        result
    }

    fn handle_message(&mut self, _from: NodeId, msg: Self::Message) -> EventResult<Self> {
        match msg {
            TestMessage::Ping { from, slot } => {
                self.tracker.track_test_event(
                    self.id,
                    "ping_received",
                    &format!("from={from},slot={slot}"),
                );
                let mut result = EventResult::default();
                result.schedule_event(
                    self.clock.now() + Duration::from_millis(100),
                    TestTimedEvent::SendPong { to: from, slot },
                );
                result
            }
            TestMessage::Pong { from, slot } => {
                self.tracker.track_test_event(
                    self.id,
                    "pong_received",
                    &format!("from={from},slot={slot}"),
                );
                EventResult::default()
            }
        }
    }

    fn handle_cpu_task(&mut self, _task: Self::Task) -> EventResult<Self> {
        self.tracker
            .track_test_event(self.id, "cpu_task_completed", "");
        EventResult::default()
    }

    fn handle_timed_event(&mut self, event: Self::TimedEvent) -> EventResult<Self> {
        match event {
            TestTimedEvent::SendPong { to, slot } => {
                self.tracker.track_test_event(
                    self.id,
                    "send_pong",
                    &format!("to={to},slot={slot}"),
                );
                let mut result = EventResult::default();
                result.send_to(
                    to,
                    TestMessage::Pong {
                        from: self.id,
                        slot,
                    },
                );
                result
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Test configuration helpers
// ---------------------------------------------------------------------------

fn new_node(stake: Option<u64>, producers: Vec<&str>) -> RawNode {
    RawNode {
        stake,
        location: RawNodeLocation::Cluster {
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
                        latency_ms: 5.0,
                        bandwidth_bytes_per_second: None,
                    },
                )
            })
            .collect(),
        adversarial: None,
        behaviours: vec![],
    }
}

fn test_topology() -> RawTopology {
    // 4 fully-connected nodes
    RawTopology {
        nodes: vec![
            ("a".into(), new_node(Some(250), vec!["b", "c", "d"])),
            ("b".into(), new_node(Some(250), vec!["a", "c", "d"])),
            ("c".into(), new_node(Some(250), vec!["a", "b", "d"])),
            ("d".into(), new_node(Some(250), vec!["a", "b", "c"])),
        ]
        .into_iter()
        .collect(),
    }
}

fn test_config(shard_count: usize) -> Arc<SimConfiguration> {
    let mut params: crate::config::RawParameters =
        serde_yaml::from_slice(include_bytes!("../../../../parameters/config.default.yaml"))
            .unwrap();
    params.leios_variant = crate::config::LeiosVariant::Linear;
    params.simulate_transactions = false;
    params.shard_count = shard_count;
    let topology = test_topology().into();
    let mut config = SimConfiguration::build(params, topology).unwrap();
    config.slots = Some(NUM_SLOTS);
    Arc::new(config)
}

/// We configure the simulation to run for NUM_SLOTS slots. The last slot may
/// not fully complete (the engine terminates at the slot boundary), so we only
/// assert on the first EXPECTED_SLOTS slots.
const NUM_SLOTS: u64 = 6;
const EXPECTED_SLOTS: u64 = 5;
const NUM_NODES: usize = 4;
const PEERS_PER_NODE: usize = 3; // fully connected with 4 nodes

// ---------------------------------------------------------------------------
// Event collection and assertions
// ---------------------------------------------------------------------------

fn collect_test_events(
    rx: mpsc::UnboundedReceiver<(Event, Timestamp)>,
) -> Vec<(String, String, String, Timestamp)> {
    let mut events = vec![];
    let mut rx = rx;
    while let Ok((event, ts)) = rx.try_recv() {
        if let Event::TestNodeEvent {
            node,
            event_type,
            detail,
        } = event
        {
            events.push((node, event_type, detail, ts));
        }
    }
    events
}

fn verify_events(events: &[(String, String, String, Timestamp)], config: &SimConfiguration) {
    let slot_events: Vec<_> = events.iter().filter(|e| e.1 == "slot").collect();
    let ping_events: Vec<_> = events.iter().filter(|e| e.1 == "ping_received").collect();
    let pong_events: Vec<_> = events.iter().filter(|e| e.1 == "pong_received").collect();
    let send_pong_events: Vec<_> = events.iter().filter(|e| e.1 == "send_pong").collect();

    // Each node must have seen at least slots 0..EXPECTED_SLOTS.
    // (The engine may also deliver slot EXPECTED_SLOTS before terminating.)
    for node_config in &config.nodes {
        let node_slots: Vec<u64> = slot_events
            .iter()
            .filter(|e| e.0 == node_config.name)
            .map(|e| e.2.parse::<u64>().unwrap())
            .collect();
        for slot in 0..EXPECTED_SLOTS {
            assert!(
                node_slots.contains(&slot),
                "node {} missing slot {slot}",
                node_config.name
            );
        }
    }

    // Pings from the first EXPECTED_SLOTS slots should all have been delivered and responded to.
    // Count pings for slots 0..EXPECTED_SLOTS only.
    let expected_pings = NUM_NODES * PEERS_PER_NODE * EXPECTED_SLOTS as usize;

    let early_pings: Vec<_> = ping_events
        .iter()
        .filter(|e| {
            e.2.split(',')
                .find_map(|kv| kv.strip_prefix("slot="))
                .and_then(|s| s.parse::<u64>().ok())
                .is_some_and(|s| s < EXPECTED_SLOTS)
        })
        .collect();
    assert_eq!(
        early_pings.len(),
        expected_pings,
        "expected {expected_pings} pings for slots 0..{EXPECTED_SLOTS}, got {}",
        early_pings.len()
    );

    // Each ping should produce a send_pong and a pong_received.
    // We check totals are at least as large (the last slot may add extras).
    assert!(
        send_pong_events.len() >= expected_pings,
        "expected at least {expected_pings} send_pong events, got {}",
        send_pong_events.len()
    );
    assert!(
        pong_events.len() >= expected_pings,
        "expected at least {expected_pings} pong_received events, got {}",
        pong_events.len()
    );
}

// ---------------------------------------------------------------------------
// Run helpers
// ---------------------------------------------------------------------------

async fn run_sequential(shard_count: usize) -> Vec<(String, String, String, Timestamp)> {
    let config = test_config(shard_count);
    let (tx, rx) = mpsc::unbounded_channel();
    let mut rng = ChaChaRng::seed_from_u64(config.seed);
    let runner =
        crate::sim::sequential::build_for_test::<TestNode>(config.clone(), tx, &mut rng);
    let token = CancellationToken::new();
    tokio::task::spawn_blocking(move || runner.run(token))
    .await
    .unwrap()
    .unwrap();
    collect_test_events(rx)
}

async fn run_actor(shard_count: usize) -> Vec<(String, String, String, Timestamp)> {
    let config = test_config(shard_count);
    let (tx, rx) = mpsc::unbounded_channel();
    let sim = crate::sim::actor::ActorSimulation::new_generic::<TestNode, _>(
        config.clone(),
        tx,
        crate::sim::actor::no_additional_actors,
    )
    .unwrap();
    let token = CancellationToken::new();
    sim.run(token).await.unwrap();
    collect_test_events(rx)
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[tokio::test]
async fn test_sequential_single_shard() {
    let config = test_config(1);
    let events = run_sequential(1).await;
    verify_events(&events, &config);
}

#[tokio::test]
async fn test_sequential_multi_shard() {
    let config = test_config(2);
    let events = run_sequential(2).await;
    verify_events(&events, &config);
}

#[tokio::test]
async fn test_actor_single_shard() {
    let config = test_config(1);
    let events = run_actor(1).await;
    verify_events(&events, &config);
}

#[tokio::test]
async fn test_actor_multi_shard() {
    let config = test_config(2);
    let events = run_actor(2).await;
    verify_events(&events, &config);
}

#[tokio::test]
async fn test_sequential_deterministic() {
    let events1 = run_sequential(1).await;
    let events2 = run_sequential(1).await;
    // Strip timestamps for comparison — just compare (node, event_type, detail) sequences
    let stripped1: Vec<_> = events1.iter().map(|e| (&e.0, &e.1, &e.2)).collect();
    let stripped2: Vec<_> = events2.iter().map(|e| (&e.0, &e.1, &e.2)).collect();
    assert_eq!(stripped1, stripped2, "sequential engine should be deterministic");
}
