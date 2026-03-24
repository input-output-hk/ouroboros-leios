mod blockfetch;
mod capture;
mod chainsync;
mod connect;
mod follow;
mod handshake;
mod serve;

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
        } => serve::run(port, magic, block_rate).await,
        Command::Follow {
            host,
            magic,
            max_rollback,
        } => follow::run(&host, magic, max_rollback).await,
    }
}
