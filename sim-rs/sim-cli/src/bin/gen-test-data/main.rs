use std::{fs, path::PathBuf};

use anyhow::Result;
use clap::{Parser, Subcommand};
use sim_core::config::SimConfiguration;
use strategy::{globe, random_graph, simplified, GlobeArgs, RandomGraphArgs, SimplifiedArgs};

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
    Globe(GlobeArgs),
}

fn main() -> Result<()> {
    let args = Args::parse();

    let raw_config = match args.strategy {
        Strategy::RandomGraph(args) => random_graph(&args)?,
        Strategy::Simplified(args) => simplified(&args)?,
        Strategy::Globe(args) => globe(&args)?,
    };

    let serialized = toml::to_string_pretty(&raw_config)?;

    let full_config: SimConfiguration = raw_config.into();
    full_config.validate()?;

    fs::write(args.path, serialized)?;

    Ok(())
}
