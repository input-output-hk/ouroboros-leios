//! Submit transactions to a node via the TxSubmission protocol.
//!
//! By default submits a single random transaction and exits when it is
//! accepted. With `--tx-rate`, generates transactions on a Poisson schedule.

use std::time::Duration;

use rand::rngs::StdRng;
use rand::{Rng, SeedableRng};

use net_core::mux::{MuxConfig, ProtocolConfig};
use net_core::protocol::Role;
use net_core::protocol::Runner;
use net_core::protocols::keepalive;
use net_core::protocols::keepalive::KeepAlive;
use net_core::protocols::txsubmission;
use net_core::protocols::txsubmission::{PendingTx, TxBody, TxId, TxSubmission};

use crate::connect;

/// KeepAlive ping interval.
const KEEPALIVE_INTERVAL: Duration = Duration::from_secs(20);

/// Sample an exponential inter-arrival time: -ln(U) / rate
fn exp_sample(rng: &mut StdRng, rate: f64) -> Duration {
    let u: f64 = rng.gen_range(0.001..1.0);
    Duration::from_secs_f64(-u.ln() / rate)
}

/// Generate a random PendingTx with the given size range.
fn generate_random_tx(rng: &mut StdRng, min_size: usize, max_size: usize) -> PendingTx {
    let size = if min_size == max_size {
        min_size
    } else {
        rng.gen_range(min_size..=max_size)
    };

    // TxId: random 32 bytes encoded as CBOR bytes.
    let mut hash = [0u8; 32];
    rng.fill(&mut hash);
    let mut id_buf = Vec::new();
    let mut enc = minicbor::Encoder::new(&mut id_buf);
    enc.bytes(&hash).expect("CBOR encode tx id");

    // TxBody: random bytes of the desired size, encoded as CBOR bytes.
    let mut payload = vec![0u8; size];
    rng.fill(payload.as_mut_slice());
    let mut body_buf = Vec::new();
    let mut enc = minicbor::Encoder::new(&mut body_buf);
    enc.bytes(&payload).expect("CBOR encode tx body");

    PendingTx {
        tx_id: TxId(id_buf),
        body: TxBody(body_buf),
        size: size as u32,
    }
}

pub async fn run(
    host: &str,
    magic: u64,
    tx_rate: Option<f64>,
    min_size: usize,
    max_size: usize,
    count: Option<usize>,
) -> Result<(), Box<dyn std::error::Error>> {
    println!("connecting to {host}...");

    let ts_proto = ProtocolConfig {
        id: txsubmission::PROTOCOL_ID,
        priority: 3,
        ingress_limit: txsubmission::INGRESS_LIMIT,
        egress_queue_size: 16,
    };
    let ka_proto = ProtocolConfig {
        id: keepalive::PROTOCOL_ID,
        priority: 7,
        ingress_limit: keepalive::INGRESS_LIMIT,
        egress_queue_size: 4,
    };

    let mux_config = MuxConfig {
        sdu_timeout: Duration::from_secs(900),
        ..MuxConfig::default()
    };

    let conn =
        connect::connect_and_handshake_with_config(host, magic, &[ts_proto, ka_proto], mux_config)
            .await?;

    let mut channels = conn.channels.into_iter();
    let (ts_send, ts_recv) = channels.next().expect("txsubmission channel");
    let (ka_send, ka_recv) = channels.next().expect("keepalive channel");

    // Spawn keepalive background task.
    let ka_handle = tokio::spawn(async move {
        let mut runner = Runner::<KeepAlive>::new(Role::Client, ka_send, ka_recv);
        let mut cookie: u16 = 0;
        loop {
            tokio::time::sleep(KEEPALIVE_INTERVAL).await;
            cookie = cookie.wrapping_add(1);
            if keepalive::keep_alive(&mut runner, cookie).await.is_err() {
                break;
            }
        }
    });

    // Create the tx channel.
    let (tx_sender, mut tx_receiver) = tokio::sync::mpsc::channel::<PendingTx>(16);

    // Determine how many txs to generate.
    let total = match (tx_rate, count) {
        (None, None) => 1usize,        // single tx mode
        (None, Some(n)) => n,          // fixed count, no delay
        (Some(_), None) => usize::MAX, // infinite stream
        (Some(_), Some(n)) => n,       // stream with limit
    };

    let rate_desc = match tx_rate {
        Some(r) => format!(" at {r}/sec (~{:.1}s mean interval)", 1.0 / r),
        None => String::new(),
    };
    println!(
        "submitting {}{rate_desc}, size {}..{} bytes",
        if total == usize::MAX {
            "unlimited txs".to_string()
        } else if total == 1 {
            "1 tx".to_string()
        } else {
            format!("{total} txs")
        },
        min_size,
        max_size
    );

    // Spawn tx generator task.
    let generator = tokio::spawn(async move {
        let mut rng = StdRng::from_entropy();

        for i in 0..total {
            if let Some(rate) = tx_rate {
                if i > 0 {
                    let interval = exp_sample(&mut rng, rate);
                    tokio::time::sleep(interval).await;
                }
            }

            let tx = generate_random_tx(&mut rng, min_size, max_size);
            println!("  generated tx #{} ({} bytes)", i + 1, tx.size);
            if tx_sender.send(tx).await.is_err() {
                break; // client protocol finished
            }
        }
        // Drop sender to signal no more txs.
    });

    // Run the client protocol.
    let mut runner = Runner::<TxSubmission>::new(Role::Client, ts_send, ts_recv);
    let result = txsubmission::run_client(&mut runner, &mut tx_receiver).await;

    match &result {
        Ok(()) => println!("txsubmission complete"),
        Err(e) => println!("txsubmission error: {e}"),
    }

    generator.abort();
    ka_handle.abort();
    conn.running.abort();

    result.map_err(|e| e.into())
}
