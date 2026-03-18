use std::{collections::HashMap, sync::Arc};

use anyhow::Result;
use futures::future::BoxFuture;
use rand::RngCore;
use rand_chacha::{ChaChaRng, rand_core::SeedableRng};
use tokio::{select, sync::mpsc, task::JoinSet};
use tokio_util::sync::CancellationToken;

use crate::{
    clock::{Clock, ClockCoordinator, Timestamp},
    config::{LeiosVariant, NodeId, SimConfiguration},
    events::EventTracker,
    model::Transaction,
    network::{Network, ShardLookup},
    sharding::shard::{Shard, build_shards},
};

use super::{
    MiniProtocol, NodeImpl,
    driver::NodeDriver,
    leios::LeiosNode,
    linear_leios::LinearLeiosNode,
    slot::SlotWitness,
    stracciatella::StracciatellaLeiosNode,
};

pub(crate) trait Actor {
    fn run(self: Box<Self>) -> BoxFuture<'static, Result<()>>;
}

pub(crate) struct ActorInitArgs<'a, N: NodeImpl> {
    pub config: Arc<SimConfiguration>,
    pub clock: Clock,
    pub tracker: EventTracker,
    pub nodes: &'a mut [N],
}

fn no_additional_actors<N: NodeImpl>(_args: ActorInitArgs<N>) -> Vec<Box<dyn Actor>> {
    vec![]
}

enum NodeListWrapper {
    Leios(Vec<NodeDriver<LeiosNode>>),
    Stracciatella(Vec<NodeDriver<StracciatellaLeiosNode>>),
    LinearLeios(Vec<NodeDriver<LinearLeiosNode>>),
}

impl NodeListWrapper {
    fn run_all(&mut self, set: &mut JoinSet<Result<()>>) {
        match self {
            Self::Leios(nodes) => {
                for node in nodes.drain(..) {
                    set.spawn(node.run());
                }
            }
            Self::Stracciatella(nodes) => {
                for node in nodes.drain(..) {
                    set.spawn(node.run());
                }
            }
            Self::LinearLeios(nodes) => {
                for node in nodes.drain(..) {
                    set.spawn(node.run());
                }
            }
        }
    }
}

pub(super) struct ActorSimulation {
    shards: Vec<Shard>,
    slot_witness: SlotWitness,
    nodes: NodeListWrapper,
    actors: Vec<Box<dyn Actor>>,
}

impl ActorSimulation {
    pub fn new(
        config: Arc<SimConfiguration>,
        event_sender: mpsc::UnboundedSender<(crate::events::Event, Timestamp)>,
    ) -> Result<Self> {
        let shard_count = config.shard_count;
        let shard_lookup: ShardLookup = crate::sharding::compute_shard_lookup(&config);

        let mut clock_coordinators: Vec<ClockCoordinator> = (0..shard_count)
            .map(|_| ClockCoordinator::new(config.timestamp_resolution))
            .collect();
        let clocks: Vec<Clock> = clock_coordinators.iter().map(|cc| cc.clock()).collect();
        let trackers: Vec<EventTracker> = clocks
            .iter()
            .map(|clock| EventTracker::new(event_sender.clone(), clock.clone(), &config.nodes))
            .collect();

        let (nodes, actors, shards) = match config.variant {
            LeiosVariant::Linear | LeiosVariant::LinearWithTxReferences => {
                let (nodes, actors, tx_sinks, networks) = Self::init_nodes(
                    &config,
                    &trackers,
                    &clocks,
                    &shard_lookup,
                    NodeListWrapper::LinearLeios,
                    super::linear_leios::register_actors,
                )?;
                let shards = build_shards(
                    &config,
                    &clocks,
                    &mut clock_coordinators,
                    &shard_lookup,
                    tx_sinks,
                    networks,
                );
                (nodes, actors, shards)
            }
            LeiosVariant::FullWithoutIbs => {
                let (nodes, actors, tx_sinks, networks) = Self::init_nodes(
                    &config,
                    &trackers,
                    &clocks,
                    &shard_lookup,
                    NodeListWrapper::Stracciatella,
                    no_additional_actors,
                )?;
                let shards = build_shards(
                    &config,
                    &clocks,
                    &mut clock_coordinators,
                    &shard_lookup,
                    tx_sinks,
                    networks,
                );
                (nodes, actors, shards)
            }
            _ => {
                let (nodes, actors, tx_sinks, networks) = Self::init_nodes(
                    &config,
                    &trackers,
                    &clocks,
                    &shard_lookup,
                    NodeListWrapper::Leios,
                    no_additional_actors,
                )?;
                let shards = build_shards(
                    &config,
                    &clocks,
                    &mut clock_coordinators,
                    &shard_lookup,
                    tx_sinks,
                    networks,
                );
                (nodes, actors, shards)
            }
        };

        let slot_witness = SlotWitness::new(clocks[0].barrier(), trackers[0].clone(), &config);

        Ok(Self {
            shards,
            slot_witness,
            nodes,
            actors,
        })
    }

    #[allow(clippy::type_complexity, clippy::too_many_arguments)]
    fn init_nodes<N, NLF, AAF>(
        config: &Arc<SimConfiguration>,
        trackers: &[EventTracker],
        clocks: &[Clock],
        shard_lookup: &ShardLookup,
        node_list_wrapper_fn: NLF,
        additional_actors_fn: AAF,
    ) -> Result<(
        NodeListWrapper,
        Vec<Box<dyn Actor>>,
        Vec<HashMap<NodeId, mpsc::UnboundedSender<Arc<Transaction>>>>,
        Vec<Network<MiniProtocol, N::Message>>,
    )>
    where
        N: NodeImpl,
        N::Message: Send + 'static,
        NLF: FnOnce(Vec<NodeDriver<N>>) -> NodeListWrapper,
        AAF: FnOnce(ActorInitArgs<N>) -> Vec<Box<dyn Actor>>,
    {
        let shard_count = clocks.len();
        let mut rng = ChaChaRng::seed_from_u64(config.seed);

        let mut networks: Vec<Network<MiniProtocol, N::Message>> = clocks
            .iter()
            .map(|clock| Network::new(clock.clone()))
            .collect();

        let mut node_impls = vec![];
        for node_config in &config.nodes {
            let shard = shard_lookup[&node_config.id];
            node_impls.push(N::new(
                node_config,
                config.clone(),
                trackers[shard].clone(),
                ChaChaRng::seed_from_u64(rng.next_u64()),
                clocks[shard].clone(),
            ));
        }

        let actor_args = ActorInitArgs {
            config: config.clone(),
            clock: clocks[0].clone(),
            tracker: trackers[0].clone(),
            nodes: &mut node_impls,
        };
        let actors = additional_actors_fn(actor_args);

        let mut per_shard_tx_sinks: Vec<HashMap<NodeId, mpsc::UnboundedSender<Arc<Transaction>>>> =
            (0..shard_count).map(|_| HashMap::new()).collect();
        let mut all_nodes = vec![];
        for (node_config, node) in config.nodes.iter().zip(node_impls) {
            let id = node_config.id;
            let shard = shard_lookup[&id];
            let (tx_sink, tx_source) = mpsc::unbounded_channel();
            per_shard_tx_sinks[shard].insert(id, tx_sink);
            let driver = NodeDriver::new(
                node,
                node_config,
                config.clone(),
                &mut networks[shard],
                tx_source,
                trackers[shard].clone(),
                clocks[shard].barrier(),
            );
            all_nodes.push(driver);
        }

        Ok((
            node_list_wrapper_fn(all_nodes),
            actors,
            per_shard_tx_sinks,
            networks,
        ))
    }

    pub async fn run(mut self, token: CancellationToken) -> Result<()> {
        let mut set = JoinSet::new();

        self.nodes.run_all(&mut set);
        for actor in self.actors {
            set.spawn(actor.run());
        }

        if self.shards.len() == 1 {
            let shard = self.shards.pop().unwrap();
            select! {
                biased;
                _ = token.cancelled() => {}
                _ = self.slot_witness.run() => {}
                result = shard.run(token.clone()) => { result? }
                result = set.join_next() => { result.unwrap()??; }
            };
        } else {
            let mut slot_witness = self.slot_witness;
            let slot_token = token.clone();
            set.spawn(async move {
                select! {
                    _ = slot_token.cancelled() => {}
                    _ = slot_witness.run() => { slot_token.cancel(); }
                }
                Ok(())
            });

            for shard in self.shards {
                let shard_token = token.clone();
                set.spawn(shard.run(shard_token));
            }

            while let Some(result) = set.join_next().await {
                match result {
                    Ok(Ok(())) => {}
                    Ok(Err(e)) => {
                        if !token.is_cancelled() {
                            token.cancel();
                            return Err(e);
                        }
                    }
                    Err(e) => {
                        if !token.is_cancelled() {
                            token.cancel();
                            return Err(e.into());
                        }
                    }
                }
            }
        }

        Ok(())
    }
}
