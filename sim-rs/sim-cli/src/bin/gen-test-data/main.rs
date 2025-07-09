use std::{fs, path::PathBuf};

use anyhow::Result;
use clap::{Parser, Subcommand};
use sim_core::config::Topology;
use strategy::{
    GlobeArgs, OrganicArgs, RandomGraphArgs, SimplifiedArgs, globe, organic, random_graph,
    simplified,
};

mod strategy;

#[derive(Debug, Parser)]
struct Args {
    path: PathBuf,
    #[command(subcommand)]
    strategy: Strategy,
}

#[derive(Debug, Subcommand)]
enum Strategy {
    Organic(OrganicArgs),
    RandomGraph(RandomGraphArgs),
    Simplified(SimplifiedArgs),
    Globe(GlobeArgs),
}

fn main() -> Result<()> {
    let args = Args::parse();

    let raw_topology = match args.strategy {
        Strategy::RandomGraph(args) => random_graph(&args)?,
        Strategy::Simplified(args) => simplified(&args)?,
        Strategy::Globe(args) => globe(&args)?,
        Strategy::Organic(args) => organic(&args)?,
    };

    let serialized = serde_yaml::to_string(&raw_topology.clone().into_topology())?;

    let topology: Topology = raw_topology.into_topology().into();
    topology.validate()?;

    fs::write(args.path, serialized)?;

    Ok(())
}
