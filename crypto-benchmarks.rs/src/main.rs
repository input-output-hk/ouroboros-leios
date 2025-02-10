use clap::{Parser, Subcommand};
use hex::ToHex;
use num_bigint::BigInt;
use num_rational::Ratio;
use num_traits::FromPrimitive;
use quickcheck::{Arbitrary,Gen};
use serde_cbor;
use std::io::{Error, ErrorKind};
use std::path::PathBuf;
use std::process;

use leios_crypto_benchmarks::key::*;
use leios_crypto_benchmarks::primitive::*;
use leios_crypto_benchmarks::realism::*;
use leios_crypto_benchmarks::sortition::*;
use leios_crypto_benchmarks::vote::*;

#[derive(Parser)]
#[command(version, about, long_about = None)]
struct Cli {
    name: Option<String>,
    #[arg(long)]
    verbose: bool,
    #[command(subcommand)]
    command: Option<Commands>,
}

#[derive(Subcommand)]
enum Commands {
    GenEid,
    GenEbHash,
    GenPoolKeyHash,
    GenStake {
        #[arg(long)]
       pools: usize,
       #[arg(long)]
       total: Coin,
       #[arg(long)]
       stake_file: PathBuf,
    },
    GenPools {
        #[arg(long)]
       pools: usize,
       #[arg(long)]
       total: Coin,
       #[arg(long)]
       pools_file: PathBuf,
    },
    GenKey {
        #[arg(long)]
        sec_file: PathBuf,
        #[arg(long)]
        pub_file: PathBuf,
        #[arg(long)]
        pop_file: PathBuf,
    },
    RegisterKey {
        #[arg(long)]
        pool: PoolKeyhash,
        #[arg(long)]
        pub_file: PathBuf,
        #[arg(long)]
        pop_file: PathBuf,
        #[arg(long)]
        reg_file: PathBuf,
    },
    CheckPop {
        #[arg(long)]
        pub_file: PathBuf,
        #[arg(long)]
        pop_file: PathBuf,
    },
    SignMessage {
        #[arg(long)]
        sec_file: PathBuf,
        #[arg(long)]
        dst: String,
        #[arg(long)]
        msg_file: PathBuf,
        #[arg(long)]
        sig_file: PathBuf,
    },
    VerifyMessage {
        #[arg(long)]
        pub_file: PathBuf,
        #[arg(long)]
        dst: String,
        #[arg(long)]
        msg_file: PathBuf,
        #[arg(long)]
        sig_file: PathBuf,
    },
    CountVotes {
        #[arg(long)]
        sec_file: PathBuf,
        #[arg(long, value_parser=Eid::parse)]
        eid: Eid,
        #[arg(long)]
        pool_stake: Coin,
        #[arg(long)]
        total_stake: Coin,
        #[arg(long)]
        voters: usize,
    },
      CastVote {
      #[arg(long)]
      sec_file: PathBuf,
      #[arg(long)]
      pool: PoolKeyhash,
      #[arg(long, value_parser=Eid::parse)]
      eid: Eid,
      #[arg(long, value_parser=EbHash::parse)]
      eb_hash: EbHash,
      #[arg(long)]
      vote_file: PathBuf,
    },
    VerifyVote {
      #[arg(long)]
      pub_file: PathBuf,
      #[arg(long)]
      vote_file: PathBuf,
    },
}


fn main() {

    let cli = Cli::parse();

    match &cli.command {
        Some(Commands::GenEid{}) => {
            let g = &mut Gen::new(10);
            let eid = Eid::arbitrary(g);
            println!("{}", eid.0);
          }
          Some(Commands::GenEbHash{}) => {
              let g = &mut Gen::new(10);
              let ebhash = EbHash::arbitrary(g);
              println!("{}", ebhash.encode_hex::<String>());
          }
          Some(Commands::GenPoolKeyHash{}) => {
            let g = &mut Gen::new(10);
            let pool = arbitrary_poolkeyhash(g);
            println!("{}", pool.encode_hex::<String>());
          }
          Some(Commands::GenStake { pools, total , stake_file}) => {
            let g = &mut Gen::new(10);
            let stake = realistic_stake(g, *total, *pools);
            write_cbor(stake_file, &stake).unwrap();
        }
        Some(Commands::GenPools { pools, total , pools_file}) => {
            let g = &mut Gen::new(10);
            let stake = realistic_pools(g, *total, *pools);
            write_cbor(pools_file, &stake).unwrap();
        }
          Some(Commands::GenKey {sec_file, pub_file, pop_file}) => {
            let (sec_key, pub_key, proof) = key_gen();
            write_cbor(sec_file, &sec_key).unwrap();
            write_cbor(pub_file, &pub_key).unwrap();
            write_cbor(pop_file, &proof).unwrap();
        }
        Some(Commands::RegisterKey { pool, pub_file, pop_file, reg_file }) => {
            let pub_key: PubKey = read_cbor(pub_file).unwrap();
            let proof: PoP = read_cbor(pop_file).unwrap();
            let reg = Reg {pool: *pool, mvk: pub_key, mu: proof, kes_sig: KesSig::null()};
            write_cbor(reg_file, &reg).unwrap();
        }
        Some(Commands::CheckPop { pub_file, pop_file }) => {
            let pub_key: PubKey = read_cbor(pub_file).unwrap();
            let proof: PoP = read_cbor(pop_file).unwrap();
            let result = check_pop(&pub_key, &proof);
            if cli.verbose {
                if result {
                    println!("Proof of possesion verified.");
                } else {
                    println!("Invalid proof of possession.");
                }
            }
            process::exit(if result {0} else {-1});
        }
        Some(Commands::SignMessage { sec_file, dst, msg_file, sig_file }) => {
            let sec_key: SecKey = read_cbor(sec_file).unwrap();
            let msg: Vec<u8> = std::fs::read(msg_file).unwrap();
            let sig = sign_message(&sec_key, dst.as_bytes(), &msg);
            write_cbor(sig_file, &sig).unwrap();
        }
        Some(Commands::VerifyMessage { pub_file, dst, msg_file, sig_file }) => {
            let pub_key: PubKey = read_cbor(pub_file).unwrap();
            let msg: Vec<u8> = std::fs::read(msg_file).unwrap();
            let sig : Sig = read_cbor(sig_file).unwrap();
            let result = verify_message(&pub_key, dst.as_bytes(), &msg, &sig);
            if cli.verbose {
                if result {
                    println!("Signature verified.");
                } else {
                    println!("Invalid signature.");
                }
            }
            process::exit(if result {0} else {-1});
        }
        Some(Commands::CountVotes { sec_file, eid, pool_stake, total_stake, voters }) => {
           let sec_key: SecKey = read_cbor(sec_file).unwrap();
           let sig = gen_sigma_eid(eid, &sec_key);
           let p = sig.to_rational();
           let s = Ratio::new(BigInt::from_u64(*pool_stake).unwrap(), BigInt::from_u64(*total_stake).unwrap());
           let votes = voter_check(*voters, &s, &p);
           if cli.verbose {
            eprintln!("Stake fraction: {}", s);
            eprintln!("Probability: {}", p);
            eprintln!("Vote fraction: {}/{}", votes, voters);
        }
           println!("{}", votes);
        }
        Some(Commands::CastVote { sec_file, pool, eid, eb_hash, vote_file }) => {
            let sec_key: SecKey = read_cbor(sec_file).unwrap();
            let vote: Vote = gen_vote_nonpersistent(pool, eid, eb_hash, &sec_key);
            write_cbor(vote_file, &vote).unwrap();
        }   
        Some(Commands::VerifyVote { pub_file, vote_file }) => {
            let pub_key: PubKey = read_cbor(pub_file).unwrap();
            let vote: Vote = read_cbor(vote_file).unwrap();
            let result = verify_vote(&pub_key, &vote);
            if cli.verbose {
                if result {
                    println!("Vote verified.");
                } else {
                    println!("Invalid vote.");
                }
            }
            process::exit(if result {0} else {-1});
        }
        None => {}
    }

}

fn write_cbor<A>(path: &PathBuf, item: &A) -> Result<(), Error>
where
    A: serde::Serialize,
{
    let cbor =
      serde_cbor::to_vec(&item)
      .map_err(|e| Error::new(ErrorKind::Other, e))?;
    std::fs::write(path, cbor)
}

fn read_cbor<A>(path: &PathBuf) -> Result<A, Error>
where
    A: serde::de::DeserializeOwned,
{
    let cbor = std::fs::read(path)?;
    let item: A =
      serde_cbor::from_slice(&cbor)
      .map_err(|e| Error::new(ErrorKind::Other, e))?;
    Ok(item)
}
