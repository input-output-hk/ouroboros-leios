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
    input: PathBuf,

    /// Output report file (optional)
    #[arg(short, long)]
    output: Option<PathBuf>,
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let opt = Opt::parse();

    // Read and parse topology file
    let content = fs::read_to_string(&opt.input)?;
    let topology: Topology = serde_yaml::from_str(&content)?;

    // Generate report
    let report = report::generate_report(&topology, opt.input.to_str().unwrap_or("unknown"));

    // Output report
    match opt.output {
        Some(path) => fs::write(path, report)?,
        None => println!("{}", report),
    }

    Ok(())
}
