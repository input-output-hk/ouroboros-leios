use clap::Parser;
use std::fs;
use std::path::PathBuf;

mod analysis;
mod models;
mod report;

use models::Topology;

#[derive(Debug, Parser)]
#[command(name = "topology-checker", about = "Analyze network topology files")]
struct Opt {
    /// Input topology file
    #[arg(short, long)]
    input: Option<PathBuf>,

    /// Output report file (optional)
    #[arg(short, long)]
    output: Option<PathBuf>,

    /// Starting node for hop analysis (optional)
    #[arg(short = 'n', long)]
    start_node: Option<String>,
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let opt = Opt::parse();
    let input = opt
        .input
        .unwrap_or_else(|| "../simulation/test/data/simulation/topo-default-100.yaml".into());

    // Read and parse topology file
    let content = fs::read_to_string(&input)?;
    let topology: Topology = serde_yaml::from_str(&content)?;

    // Validate start node if provided
    if let Some(ref node) = opt.start_node {
        if !topology.nodes.contains_key(node) {
            return Err(format!("Start node '{}' not found in topology", node).into());
        }
    }

    // Generate report
    let report = report::generate_report(
        &topology,
        input.to_str().unwrap_or("unknown"),
        opt.start_node.as_deref(),
    );

    // Output report
    match opt.output {
        Some(path) => fs::write(path, report)?,
        None => println!("{}", report),
    }

    Ok(())
}
