use std::{collections::HashSet, fs, path::PathBuf};

use anyhow::Result;
use clap::{Parser, Subcommand};
use sim_core::config::{DistributionConfig, RawConfig, SimConfiguration};
use strategy::{random_graph, simplified, RandomGraphArgs, SimplifiedArgs};

mod strategy;

#[derive(Debug, Parser)]
struct Args {
    path: PathBuf,
    #[command(subcommand)]
    strategy: Strategy,
}

#[derive(Debug, Subcommand)]
enum Strategy {
    RandomGraph(RandomGraphArgs),
    Simplified(SimplifiedArgs),
}

fn main() -> Result<()> {
    let args = Args::parse();

    let (nodes, links) = match args.strategy {
        Strategy::RandomGraph(args) => random_graph(&args)?,
        Strategy::Simplified(args) => simplified(&args)?,
    };

    let raw_config = RawConfig {
        seed: None,
        timescale: None,
        slots: None,
        nodes,
        trace_nodes: HashSet::new(),
        links,
        block_generation_probability: 0.05,
        ib_generation_probability: 5.0,
        eb_generation_probability: 5.0,
        ib_shards: 8,
        max_block_size: 90112,
        stage_length: 2,
        deliver_stage_count: 2,
        uniform_ib_generation: true,
        max_ib_requests_per_peer: 1,
        max_ib_size: 327680,
        max_tx_size: 16384,
        transaction_frequency_ms: DistributionConfig::Exp {
            lambda: 0.85,
            scale: Some(1000.0),
        },
        transaction_size_bytes: DistributionConfig::LogNormal {
            mu: 6.833,
            sigma: 1.127,
        },
    };

    let serialized = toml::to_string_pretty(&raw_config)?;

    let full_config: SimConfiguration = raw_config.into();
    full_config.validate()?;

    fs::write(args.path, serialized)?;

    Ok(())
}
