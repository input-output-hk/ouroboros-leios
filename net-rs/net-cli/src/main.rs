mod blockfetch;
mod capture;
mod chainsync;
mod connect;
mod follow;
mod handshake;
mod serve;
mod submit;

use clap::{Parser, Subcommand};
use net_core::protocols::handshake::n2n;

#[derive(Parser)]
#[command(name = "net-cli", about = "Cardano network protocol test tool")]
struct Cli {
    #[command(subcommand)]
    command: Command,
}

#[derive(Subcommand)]
enum Command {
    /// Connect to a node and perform a version handshake
    Handshake {
        /// Host and port to connect to (e.g., relay:3001)
        host: String,

        /// Network magic number
        #[arg(long, default_value_t = n2n::MAINNET_MAGIC)]
        magic: u64,
    },

    /// Capture raw handshake bytes from a node for test vectors
    Capture {
        /// Host and port to connect to
        host: String,

        /// Network magic number
        #[arg(long, default_value_t = n2n::MAINNET_MAGIC)]
        magic: u64,
    },

    /// Follow the chain tip via ChainSync (limited count, for debugging)
    ChainSync {
        /// Host and port to connect to
        host: String,

        /// Network magic number
        #[arg(long, default_value_t = n2n::MAINNET_MAGIC)]
        magic: u64,

        /// Number of headers to follow
        #[arg(long, default_value_t = 20)]
        count: usize,
    },

    /// Fetch blocks via BlockFetch (uses ChainSync to find tip first)
    BlockFetch {
        /// Host and port to connect to
        host: String,

        /// Network magic number
        #[arg(long, default_value_t = n2n::MAINNET_MAGIC)]
        magic: u64,
    },

    /// Run a fake Cardano node serving synthetic blocks
    Serve {
        /// Port to listen on
        #[arg(long, default_value_t = 3001)]
        port: u16,

        /// Network magic number
        #[arg(long, default_value_t = n2n::MAINNET_MAGIC)]
        magic: u64,

        /// Block generation rate (blocks/sec, Poisson λ)
        #[arg(long, default_value_t = 0.05)]
        block_rate: f64,

        /// Rollback rate (rollbacks/sec, Poisson λ; 0 = no rollbacks)
        #[arg(long, default_value_t = 0.0)]
        rollback_rate: f64,

        /// Maximum rollback depth (capped at chain length - 1)
        #[arg(long, default_value_t = 3)]
        max_rollback_depth: usize,
    },

    /// Submit random transactions via TxSubmission
    Submit {
        /// Host and port to connect to
        host: String,

        /// Network magic number
        #[arg(long, default_value_t = n2n::MAINNET_MAGIC)]
        magic: u64,

        /// Tx generation rate (per second, Poisson). Omit for single tx.
        #[arg(long)]
        tx_rate: Option<f64>,

        /// Minimum tx body size in bytes
        #[arg(long, default_value_t = 1500)]
        min_size: usize,

        /// Maximum tx body size in bytes
        #[arg(long, default_value_t = 1500)]
        max_size: usize,

        /// Number of transactions to submit (default: 1 if no --tx-rate, infinite otherwise)
        #[arg(long)]
        count: Option<usize>,
    },

    /// Follow the chain tip continuously with reconnection
    Follow {
        /// Host and port to connect to
        host: String,

        /// Network magic number
        #[arg(long, default_value_t = n2n::MAINNET_MAGIC)]
        magic: u64,

        /// Maximum rollback depth (number of points to retain)
        #[arg(long, default_value_t = 2160)]
        max_rollback: usize,
    },
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    tracing_subscriber::fmt::init();

    let cli = Cli::parse();

    match cli.command {
        Command::Handshake { host, magic } => handshake::run(&host, magic).await,
        Command::Capture { host, magic } => capture::run(&host, magic).await,
        Command::ChainSync { host, magic, count } => chainsync::run(&host, magic, count).await,
        Command::BlockFetch { host, magic } => blockfetch::run(&host, magic).await,
        Command::Serve {
            port,
            magic,
            block_rate,
            rollback_rate,
            max_rollback_depth,
        } => serve::run(port, magic, block_rate, rollback_rate, max_rollback_depth).await,
        Command::Submit {
            host,
            magic,
            tx_rate,
            min_size,
            max_size,
            count,
        } => submit::run(&host, magic, tx_rate, min_size, max_size, count).await,
        Command::Follow {
            host,
            magic,
            max_rollback,
        } => follow::run(&host, magic, max_rollback).await,
    }
}
