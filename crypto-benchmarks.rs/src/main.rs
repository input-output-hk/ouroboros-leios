use clap::{Parser, Subcommand};
use hex::ToHex;
use num_bigint::BigInt;
use num_rational::Ratio;
use num_traits::{FromPrimitive, ToPrimitive};
use quickcheck::{Arbitrary, Gen};
use std::collections::BTreeMap;
use std::io::{Error, ErrorKind};
use std::path::PathBuf;
use std::process;

use leios_crypto_benchmarks::cert::*;
use leios_crypto_benchmarks::fait_accompli::*;
use leios_crypto_benchmarks::key::*;
use leios_crypto_benchmarks::primitive::*;
use leios_crypto_benchmarks::registry::*;
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
    #[command(about = "Cast a single vote")]
    CastVote {
        #[arg(long)]
        seckey_file: PathBuf,
        #[arg(long)]
        pool: PoolKeyhash,
        #[arg(long, value_parser=Eid::parse)]
        eid: Eid,
        #[arg(long, value_parser=EbHash::parse)]
        eb_hash: EbHash,
        #[arg(long)]
        vote_file: PathBuf,
    },
    #[command(about = "Cast votes by many stakepools")]
    CastVotes {
        #[arg(long)]
        registry_file: PathBuf,
        #[arg(long, value_parser=Eid::parse)]
        eid: Eid,
        #[arg(long, value_parser=EbHash::parse)]
        eb_hash: EbHash,
        #[arg(long)]
        fraction_voting: f64,
        #[arg(long)]
        votes_file: PathBuf,
    },
    #[command(about = "Run the 'fait accompli' algorithm to select the persistent voters")]
    FaitAccompli {
        #[arg(long)]
        voter_count: usize,
        #[arg(long)]
        stake_file: PathBuf,
        #[arg(long)]
        fa_file: PathBuf,
    },
    #[command(about = "Generate a random hash of an endorser block (EB)")]
    GenEbHash,
    #[command(about = "Generate a random election identifier")]
    GenEid,
    #[command(about = "Generate a random stakepool identifier")]
    GenKey {
        #[arg(long)]
        seckey_file: PathBuf,
        #[arg(long)]
        pubkey_file: PathBuf,
        #[arg(long)]
        pop_file: PathBuf,
    },
    #[command(about = "Generate a random stakepool identifier")]
    GenPoolKeyHash,
    #[command(about = "Generate keys for many stakepools")]
    GenPools {
        #[arg(long)]
        stake_file: PathBuf,
        #[arg(long)]
        pools_file: PathBuf,
    },
    #[command(about = "Generate a random set of pools and their stake")]
    GenStake {
        #[arg(long)]
        pool_count: usize,
        #[arg(long)]
        total_stake: Coin,
        #[arg(long)]
        shape_alpha: f64,
        #[arg(long)]
        shape_beta: f64,
        #[arg(long)]
        stake_file: PathBuf,
    },
    #[command(about = "Determine how many votes a stakepool has in an election")]
    HasVotes {
        #[arg(long)]
        seckey_file: PathBuf,
        #[arg(long, value_parser=Eid::parse)]
        eid: Eid,
        #[arg(long)]
        pool_stake: Coin,
        #[arg(long)]
        total_stake: Coin,
        #[arg(long)]
        voter_count: usize,
    },
    #[command(about = "Build a certificate")]
    MakeCertificate {
        #[arg(long)]
        registry_file: PathBuf,
        #[arg(long)]
        votes_file: PathBuf,
        #[arg(long)]
        certificate_file: PathBuf,
    },
    #[command(about = "Assemble a local registry of public information about stakepools")]
    MakeRegistry {
        #[arg(long)]
        pools_file: PathBuf,
        #[arg(long)]
        voter_count: usize,
        #[arg(long)]
        registry_file: PathBuf,
    },
    #[command(about = "Bundle the information for registering a BLS key with other stakepools")]
    RegisterKey {
        #[arg(long)]
        pool: PoolKeyhash,
        #[arg(long)]
        pubkey_file: PathBuf,
        #[arg(long)]
        pop_file: PathBuf,
        #[arg(long)]
        registration_file: PathBuf,
    },
    #[command(about = "Sign a message")]
    SignMessage {
        #[arg(long)]
        seckey_file: PathBuf,
        #[arg(long)]
        domain_separator: String,
        #[arg(long)]
        message_file: PathBuf,
        #[arg(long)]
        signature_file: PathBuf,
    },
    #[command(about = "Verify the cryptographic validity of a certificate")]
    VerifyCertificate {
        #[arg(long)]
        registry_file: PathBuf,
        #[arg(long)]
        certificate_file: PathBuf,
    },
    #[command(about = "Verify the cryptographic validity a proof of possession")]
    VerifyPop {
        #[arg(long)]
        pubkey_file: PathBuf,
        #[arg(long)]
        pop_file: PathBuf,
    },
    #[command(about = "Verify that a certificate attests to a particular quorum")]
    VerifyQuorum {
        #[arg(long)]
        registry_file: PathBuf,
        #[arg(long)]
        certificate_file: PathBuf,
        #[arg(long)]
        quorum_fraction: f64,
    },
    #[command(about = "Verify the signature of a message")]
    VerifySignature {
        #[arg(long)]
        pubkey_file: PathBuf,
        #[arg(long)]
        domain_separator: String,
        #[arg(long)]
        message_file: PathBuf,
        #[arg(long)]
        signature_file: PathBuf,
    },
    #[command(about = "Verify the cryptographic validity of a vote")]
    VerifyVote {
        #[arg(long)]
        pubkey_file: PathBuf,
        #[arg(long)]
        vote_file: PathBuf,
    },
}

fn main() {
    let cli = Cli::parse();

    match &cli.command {
        Some(Commands::GenEid {}) => {
            let g = &mut Gen::new(10);
            let eid = Eid::arbitrary(g);
            println!("{}", eid.0);
        }
        Some(Commands::GenEbHash {}) => {
            let g = &mut Gen::new(10);
            let ebhash = EbHash::arbitrary(g);
            println!("{}", ebhash.encode_hex::<String>());
        }
        Some(Commands::GenPoolKeyHash {}) => {
            let g = &mut Gen::new(10);
            let pool = arbitrary_poolkeyhash(g);
            println!("{}", pool.encode_hex::<String>());
        }
        Some(Commands::GenKey {
            seckey_file,
            pubkey_file,
            pop_file,
        }) => {
            let (sec_key, pub_key, proof) = key_gen();
            write_cbor(seckey_file, &sec_key).unwrap();
            write_cbor(pubkey_file, &pub_key).unwrap();
            write_cbor(pop_file, &proof).unwrap();
        }
        Some(Commands::RegisterKey {
            pool,
            pubkey_file,
            pop_file,
            registration_file,
        }) => {
            let pub_key: PubKey = read_cbor(pubkey_file).unwrap();
            let proof: PoP = read_cbor(pop_file).unwrap();
            let reg = Reg {
                pool: *pool,
                mvk: pub_key,
                mu: proof,
                kes_sig: KesSig::null(),
            };
            write_cbor(registration_file, &reg).unwrap();
        }
        Some(Commands::VerifyPop {
            pubkey_file,
            pop_file,
        }) => {
            let pub_key: PubKey = read_cbor(pubkey_file).unwrap();
            let proof: PoP = read_cbor(pop_file).unwrap();
            let result = check_pop(&pub_key, &proof);
            if cli.verbose {
                if result {
                    eprintln!("Proof of possesion verified.");
                } else {
                    eprintln!("Invalid proof of possession.");
                }
            }
            process::exit(if result { 0 } else { -1 });
        }
        Some(Commands::SignMessage {
            seckey_file,
            domain_separator,
            message_file,
            signature_file,
        }) => {
            let sec_key: SecKey = read_cbor(seckey_file).unwrap();
            let msg: Vec<u8> = std::fs::read(message_file).unwrap();
            let sig = sign_message(&sec_key, domain_separator.as_bytes(), &msg);
            write_cbor(signature_file, &sig).unwrap();
        }
        Some(Commands::VerifySignature {
            pubkey_file,
            domain_separator,
            message_file,
            signature_file,
        }) => {
            let pub_key: PubKey = read_cbor(pubkey_file).unwrap();
            let msg: Vec<u8> = std::fs::read(message_file).unwrap();
            let sig: Sig = read_cbor(signature_file).unwrap();
            let result = verify_message(&pub_key, domain_separator.as_bytes(), &msg, &sig);
            if cli.verbose {
                if result {
                    eprintln!("Signature verified.");
                } else {
                    eprintln!("Invalid signature.");
                }
            }
            process::exit(if result { 0 } else { -1 });
        }
        Some(Commands::FaitAccompli {
            voter_count,
            stake_file,
            fa_file,
        }) => {
            let stake: BTreeMap<PoolKeyhash, Coin> = read_cbor(stake_file).unwrap();
            let fa = fait_accompli(&stake, *voter_count);
            write_cbor(fa_file, &fa).unwrap();
        }
        Some(Commands::HasVotes {
            seckey_file,
            eid,
            pool_stake,
            total_stake,
            voter_count,
        }) => {
            let sec_key: SecKey = read_cbor(seckey_file).unwrap();
            let sig = gen_sigma_eid(eid, &sec_key);
            let p = sig.to_rational();
            let s = Ratio::new(
                BigInt::from_u64(*pool_stake).unwrap(),
                BigInt::from_u64(*total_stake).unwrap(),
            );
            let votes = voter_check(*voter_count, &s, &p);
            if cli.verbose {
                eprintln!("Stake fraction: {}", s);
                eprintln!("Probability: {}", p);
                eprintln!("Vote fraction: {}/{}", votes, voter_count);
            }
            println!("{}", votes);
        }
        Some(Commands::CastVote {
            seckey_file,
            pool,
            eid,
            eb_hash,
            vote_file,
        }) => {
            let sec_key: SecKey = read_cbor(seckey_file).unwrap();
            let vote: Vote = gen_vote_nonpersistent(pool, eid, eb_hash, &sec_key);
            write_cbor(vote_file, &vote).unwrap();
        }
        Some(Commands::VerifyVote {
            pubkey_file,
            vote_file,
        }) => {
            let pub_key: PubKey = read_cbor(pubkey_file).unwrap();
            let vote: Vote = read_cbor(vote_file).unwrap();
            let result = verify_vote(&pub_key, &vote);
            if cli.verbose {
                if result {
                    eprintln!("Vote verified.");
                } else {
                    eprintln!("Invalid vote.");
                }
            }
            process::exit(if result { 0 } else { -1 });
        }
        Some(Commands::GenStake {
            pool_count,
            total_stake,
            shape_alpha,
            shape_beta,
            stake_file,
        }) => {
            let g = &mut Gen::new(10);
            let stake = arbitrary_stake_distribution(
                g,
                *total_stake,
                *pool_count,
                *shape_alpha,
                *shape_beta,
            );
            write_cbor(stake_file, &stake).unwrap();
        }
        Some(Commands::GenPools {
            stake_file,
            pools_file,
        }) => {
            let g = &mut Gen::new(10);
            let stake: BTreeMap<PoolKeyhash, Coin> = read_cbor(stake_file).unwrap();
            let stake = arbitrary_pools(g, &stake);
            write_cbor(pools_file, &stake).unwrap();
        }
        Some(Commands::MakeRegistry {
            pools_file,
            voter_count,
            registry_file,
        }) => {
            let pools: Vec<PoolInfo> = read_cbor(pools_file).unwrap();
            let reg = Registry::make(&pools, *voter_count);
            write_cbor(registry_file, &reg).unwrap();
        }
        Some(Commands::CastVotes {
            registry_file,
            eid,
            eb_hash,
            fraction_voting,
            votes_file,
        }) => {
            let g = &mut Gen::new(10);
            let f = (1000000. * *fraction_voting) as u32;
            let reg: Registry = read_cbor(registry_file).unwrap();
            let votes: Vec<Vote> = do_voting(&reg, eid, eb_hash)
                .into_iter()
                .filter(|_| u32::arbitrary(g) % 1000000 < f)
                .collect();
            write_cbor(votes_file, &votes).unwrap();
            if cli.verbose {
                eprintln!("Voters: {}", votes.len());
            }
        }
        Some(Commands::MakeCertificate {
            registry_file,
            votes_file,
            certificate_file,
        }) => {
            let reg: Registry = read_cbor(registry_file).unwrap();
            let votes: Vec<Vote> = read_cbor(votes_file).unwrap();
            let cert = gen_cert(&reg, &votes).unwrap();
            write_cbor(certificate_file, &cert).unwrap();
        }
        Some(Commands::VerifyCertificate {
            registry_file,
            certificate_file,
        }) => {
            let reg: Registry = read_cbor(registry_file).unwrap();
            let cert: Cert = read_cbor(certificate_file).unwrap();
            let result = verify_cert(&reg, &cert);
            if cli.verbose {
                if result {
                    eprintln!("Certificate verified.");
                } else {
                    eprintln!("Invalid certificate.");
                }
            }
            process::exit(if result { 0 } else { -1 });
        }
        Some(Commands::VerifyQuorum {
            registry_file,
            certificate_file,
            quorum_fraction,
        }) => {
            let reg: Registry = read_cbor(registry_file).unwrap();
            let cert: Cert = read_cbor(certificate_file).unwrap();
            match weigh_cert(&reg, &cert) {
                Some(weight) => {
                    let result = weight.to_ratio().to_f64().unwrap() >= *quorum_fraction;
                    if cli.verbose {
                        eprintln!("Seats in election: {}", reg.voters);
                        eprintln!("Persistent voters: {}", cert.persistent_voters.len());
                        eprintln!("Nonpersistent voters: {}", cert.nonpersistent_voters.len());
                        eprintln!(
                            "Fraction of stake: {} = {} %",
                            weight.to_ratio(),
                            100. * weight.to_ratio().to_f64().unwrap()
                        );
                        eprintln!("Quorum? {}", result);
                    }
                    process::exit(if result { 0 } else { 1 });
                }
                None => {
                    if cli.verbose {
                        eprintln!("Invalid certificate.");
                    }
                    process::exit(-1);
                }
            }
        }
        None => {
            panic!("Invalid command.");
        }
    }
}

fn write_cbor<A>(path: &PathBuf, item: &A) -> Result<(), Error>
where
    A: serde::Serialize,
{
    let cbor = serde_cbor::to_vec(&item).map_err(|e| Error::new(ErrorKind::Other, e))?;
    std::fs::write(path, cbor)
}

fn read_cbor<A>(path: &PathBuf) -> Result<A, Error>
where
    A: serde::de::DeserializeOwned,
{
    let cbor = std::fs::read(path)?;
    let item: A = serde_cbor::from_slice(&cbor).map_err(|e| Error::new(ErrorKind::Other, e))?;
    Ok(item)
}
