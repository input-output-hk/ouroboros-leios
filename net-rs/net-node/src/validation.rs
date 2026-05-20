//! Validation pipeline: pluggable `Ledger` trait + sequential validator actor.
//!
//! The `Ledger` trait abstracts block-validation work so real implementations
//! (e.g. an Acropolis-backed message ledger) can slot in without touching
//! the consensus layer. The `Validator` owns a single background task that
//! holds a `Box<dyn Ledger>` and processes `LedgerCommand`s one at a time —
//! strict sequential order is how real ledgers work (block N+1's apply
//! depends on the state left by block N), so the actor enforces it by
//! construction rather than relying on callers to serialize.
//!
//! The current concrete ledger is `FakeLedger`: it does no real work,
//! just sleeps for a configurable duration to simulate validation cost
//! and tracks the current tip so `rollback` is meaningful.

use std::fmt;
use std::time::Duration;

use async_trait::async_trait;
use net_core::types::{BlockBody, Point};
use tokio::sync::{mpsc, watch};

use crate::config::DynamicConfig;

/// Error returned by a `Ledger` implementation when `apply` or `rollback`
/// fails. Carried back to consensus inside `LedgerOutcome::*Failed`.
#[derive(Debug, Clone)]
pub struct LedgerError {
    message: String,
}

impl LedgerError {
    #[allow(dead_code)] // used by future real ledger impls + tests
    pub fn new(message: impl Into<String>) -> Self {
        Self {
            message: message.into(),
        }
    }
}

impl fmt::Display for LedgerError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.message)
    }
}

impl std::error::Error for LedgerError {}

/// A pluggable ledger that validates blocks against an internal state.
///
/// Implementations can be stateless (`FakeLedger`) or hold real ledger
/// state (future `AcropolisLedger`, backed by the message-based Apollo
/// flight control validator stack). The validator actor calls these
/// methods one at a time — the trait does not need to be internally
/// thread-safe beyond `Send`.
#[async_trait]
pub trait Ledger: Send + 'static {
    /// Apply a block on top of the current ledger state. Implementations
    /// may assume the caller has positioned the ledger at `body`'s parent
    /// (via a prior `apply` or `rollback`); if the caller breaks this
    /// contract, returning `Err` is the correct response.
    async fn apply(&mut self, point: &Point, body: &BlockBody) -> Result<(), LedgerError>;

    /// Roll the ledger state back to a previously-applied point. The
    /// target must be reachable from the current tip (or be the current
    /// tip — a no-op).
    async fn rollback(&mut self, target: &Point) -> Result<(), LedgerError>;

    /// Current tip according to the ledger's internal state. `None`
    /// means "before genesis / fresh ledger". Used for sanity checks
    /// and telemetry.
    #[allow(dead_code)] // used by tests + future diagnostics
    fn tip(&self) -> Option<Point>;
}

/// Commands submitted to the validator actor.
#[derive(Debug)]
pub enum LedgerCommand {
    /// Validate + apply a block.
    Apply { point: Point, body: BlockBody },
    /// Roll the ledger state back to an earlier point.
    Rollback { target: Point },
    /// Validate an endorser block (fake delay, then succeed).
    ValidateEb { point: Point },
    /// Validate a vote bundle (fake delay, then succeed).
    ValidateVotes {
        vote_ids: Vec<(u64, Vec<u8>)>,
        vote_data: Vec<Vec<u8>>,
    },
}

/// Outcomes reported by the validator actor after processing a command.
#[derive(Debug, Clone)]
pub enum LedgerOutcome {
    /// `apply` succeeded for `point`.
    Applied { point: Point },
    /// `rollback` succeeded to `target`.
    RolledBack { target: Point },
    /// `apply` failed for `point`.
    ApplyFailed { point: Point, error: String },
    /// `rollback` failed for `target`.
    RollbackFailed { target: Point, error: String },
    /// EB validation completed for `point`.
    EbValidated { point: Point },
    /// Vote validation completed.
    VotesValidated {
        #[allow(dead_code)] // kept for future telemetry/diagnostics
        vote_ids: Vec<(u64, Vec<u8>)>,
        vote_data: Vec<Vec<u8>>,
    },
}

/// Handle to the validator actor. Submitting work goes through `submit`;
/// completion outcomes come back via the receiver returned from `new`.
#[derive(Clone)]
pub struct Validator {
    commands: mpsc::Sender<LedgerCommand>,
}

impl Validator {
    /// Create a new validator with the default `FakeLedger` backend.
    /// Returns the handle and a receiver for outcomes.
    pub fn new(
        dyn_config: watch::Receiver<DynamicConfig>,
    ) -> (Self, mpsc::Receiver<LedgerOutcome>) {
        let ledger = Box::new(FakeLedger::new(dyn_config.clone()));
        Self::with_ledger(ledger, dyn_config)
    }

    /// Create a validator with a caller-supplied ledger. Used by tests
    /// and by future real-ledger wiring.
    pub fn with_ledger(
        ledger: Box<dyn Ledger>,
        dyn_config: watch::Receiver<DynamicConfig>,
    ) -> (Self, mpsc::Receiver<LedgerOutcome>) {
        // Bounded channels give natural backpressure: if consensus
        // submits commands faster than the ledger can process them,
        // `send().await` blocks. 64 is enough for typical per-node
        // pipelines without being so deep that a stuck ledger
        // accumulates arbitrary work.
        let (cmd_tx, cmd_rx) = mpsc::channel(64);
        let (outcome_tx, outcome_rx) = mpsc::channel(64);
        tokio::spawn(run_validator_actor(ledger, cmd_rx, outcome_tx, dyn_config));
        (Self { commands: cmd_tx }, outcome_rx)
    }

    /// Submit a `LedgerCommand` to the validator actor. Bounded
    /// channel: if the actor is behind, this awaits drain.
    pub async fn submit(&self, cmd: LedgerCommand) {
        let _ = self.commands.send(cmd).await;
    }
}

/// Actor loop: pull commands off the queue and dispatch them to the
/// ledger one at a time. Never processes two commands concurrently —
/// that's the whole point of the trait, since real ledgers have
/// inherently sequential state transitions.
async fn run_validator_actor(
    mut ledger: Box<dyn Ledger>,
    mut commands: mpsc::Receiver<LedgerCommand>,
    outcomes: mpsc::Sender<LedgerOutcome>,
    dyn_config: watch::Receiver<DynamicConfig>,
) {
    while let Some(cmd) = commands.recv().await {
        let outcome = match cmd {
            LedgerCommand::Apply { point, body } => match ledger.apply(&point, &body).await {
                Ok(()) => LedgerOutcome::Applied { point },
                Err(e) => LedgerOutcome::ApplyFailed {
                    point,
                    error: e.to_string(),
                },
            },
            LedgerCommand::Rollback { target } => match ledger.rollback(&target).await {
                Ok(()) => LedgerOutcome::RolledBack { target },
                Err(e) => LedgerOutcome::RollbackFailed {
                    target,
                    error: e.to_string(),
                },
            },
            LedgerCommand::ValidateEb { point } => {
                let ms = dyn_config.borrow().eb_validation_ms;
                tokio::time::sleep(Duration::from_secs_f64(ms / 1000.0)).await;
                LedgerOutcome::EbValidated { point }
            }
            LedgerCommand::ValidateVotes {
                vote_ids,
                vote_data,
            } => {
                let ms = dyn_config.borrow().vote_validation_ms;
                tokio::time::sleep(Duration::from_secs_f64(ms / 1000.0)).await;
                LedgerOutcome::VotesValidated {
                    vote_ids,
                    vote_data,
                }
            }
        };
        if outcomes.send(outcome).await.is_err() {
            // Receiver dropped — consensus tore down. Exit cleanly.
            return;
        }
    }
}

/// Stateless stand-in ledger used for simulation: no real validation,
/// just a configurable delay matching today's behaviour. Tracks the
/// current tip so `rollback` does something meaningful.
pub struct FakeLedger {
    dyn_config: watch::Receiver<DynamicConfig>,
    head: Option<Point>,
}

impl FakeLedger {
    pub fn new(dyn_config: watch::Receiver<DynamicConfig>) -> Self {
        Self {
            dyn_config,
            head: None,
        }
    }

    /// Compute the total validation delay for a block of the given size.
    /// Preserves the formula the old stub used so the cluster test keeps
    /// seeing the same wall-clock validation cost.
    fn block_validation_delay(&self, body_len: usize) -> Duration {
        let config = self.dyn_config.borrow();
        let ms = config.rb_head_validation_ms
            + config.rb_body_validation_ms_constant
            + config.rb_body_validation_ms_per_byte * body_len as f64;
        Duration::from_secs_f64(ms / 1000.0)
    }
}

#[async_trait]
impl Ledger for FakeLedger {
    async fn apply(&mut self, point: &Point, body: &BlockBody) -> Result<(), LedgerError> {
        let delay = self.block_validation_delay(body.raw.len());
        tokio::time::sleep(delay).await;
        self.head = Some(point.clone());
        Ok(())
    }

    async fn rollback(&mut self, target: &Point) -> Result<(), LedgerError> {
        // The fake ledger has no undo log — it just updates its head.
        // A real ledger would restore state snapshots here.
        self.head = Some(target.clone());
        Ok(())
    }

    fn tip(&self) -> Option<Point> {
        self.head.clone()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn test_dyn_config(
        head_ms: f64,
        body_const_ms: f64,
        body_per_byte: f64,
    ) -> watch::Receiver<DynamicConfig> {
        let config = DynamicConfig {
            rb_generation_probability: 0.05,
            eb_generation_probability: 0.0,
            vote_generation_probability: 0.0,
            rb_head_validation_ms: head_ms,
            rb_body_validation_ms_constant: body_const_ms,
            rb_body_validation_ms_per_byte: body_per_byte,
            eb_validation_ms: 0.0,
            vote_validation_ms: 0.0,
            tx_rate: 0.0,
        };
        watch::channel(config).1
    }

    fn fake_point(slot: u64, hash_byte: u8) -> Point {
        Point::Specific {
            slot,
            hash: [hash_byte; 32],
        }
    }

    #[test]
    fn delay_computation() {
        // Keep the original formula regression: 1 + 5 + 0.001*1000 = 7 ms.
        let rx = test_dyn_config(1.0, 5.0, 0.001);
        let fake = FakeLedger::new(rx);

        let delay = fake.block_validation_delay(1000);
        let ms = delay.as_secs_f64() * 1000.0;
        assert!((ms - 7.0).abs() < 0.01, "delay was {ms}ms, expected 7.0ms");

        let delay = fake.block_validation_delay(0);
        let ms = delay.as_secs_f64() * 1000.0;
        assert!((ms - 6.0).abs() < 0.01, "delay was {ms}ms, expected 6.0ms");
    }

    #[tokio::test]
    async fn submit_apply_returns_applied_outcome() {
        let rx = test_dyn_config(0.0, 0.0, 0.0);
        let (validator, mut outcome_rx) = Validator::new(rx);

        let point = fake_point(42, 0xAB);
        let body = BlockBody::opaque(vec![0u8; 100]);
        validator
            .submit(LedgerCommand::Apply {
                point: point.clone(),
                body,
            })
            .await;

        match outcome_rx.recv().await.expect("outcome") {
            LedgerOutcome::Applied { point: applied } => assert_eq!(applied, point),
            other => panic!("expected Applied, got {other:?}"),
        }
    }

    #[tokio::test]
    async fn submit_rollback_returns_rolled_back_outcome() {
        let rx = test_dyn_config(0.0, 0.0, 0.0);
        let (validator, mut outcome_rx) = Validator::new(rx);

        let target = fake_point(7, 0x77);
        validator
            .submit(LedgerCommand::Rollback {
                target: target.clone(),
            })
            .await;

        match outcome_rx.recv().await.expect("outcome") {
            LedgerOutcome::RolledBack { target: t } => assert_eq!(t, target),
            other => panic!("expected RolledBack, got {other:?}"),
        }
    }

    #[tokio::test]
    async fn apply_then_apply_processes_in_order() {
        // With the actor serializing commands, three Apply calls in a
        // row must complete in the same order they were submitted —
        // this is the critical invariant for strict ordered validation.
        let rx = test_dyn_config(0.0, 0.0, 0.0);
        let (validator, mut outcome_rx) = Validator::new(rx);

        let p1 = fake_point(1, 0x01);
        let p2 = fake_point(2, 0x02);
        let p3 = fake_point(3, 0x03);

        for p in [&p1, &p2, &p3] {
            validator
                .submit(LedgerCommand::Apply {
                    point: p.clone(),
                    body: BlockBody::opaque(vec![]),
                })
                .await;
        }

        for expected in [&p1, &p2, &p3] {
            match outcome_rx.recv().await.unwrap() {
                LedgerOutcome::Applied { point } => assert_eq!(&point, expected),
                other => panic!("expected Applied, got {other:?}"),
            }
        }
    }

    #[tokio::test]
    async fn fake_ledger_tracks_head_through_apply_and_rollback() {
        // Direct test of the Ledger trait (no actor). Sanity check
        // that the fake's head moves with apply and resets with
        // rollback — the property consensus relies on to decide when
        // to insert a Rollback before a subsequent Apply.
        let rx = test_dyn_config(0.0, 0.0, 0.0);
        let mut fake = FakeLedger::new(rx);

        assert!(fake.tip().is_none());

        let p1 = fake_point(1, 0x11);
        let p2 = fake_point(2, 0x22);

        fake.apply(&p1, &BlockBody::opaque(vec![])).await.unwrap();
        assert_eq!(fake.tip(), Some(p1.clone()));

        fake.apply(&p2, &BlockBody::opaque(vec![])).await.unwrap();
        assert_eq!(fake.tip(), Some(p2.clone()));

        fake.rollback(&p1).await.unwrap();
        assert_eq!(fake.tip(), Some(p1));
    }

    /// Regression: a ledger implementation that fails an `apply` must
    /// surface as `LedgerOutcome::ApplyFailed`, and the actor must keep
    /// processing subsequent commands rather than exiting.
    #[tokio::test]
    async fn apply_failure_reported_and_actor_continues() {
        struct FailFirstLedger {
            applied: bool,
        }

        #[async_trait]
        impl Ledger for FailFirstLedger {
            async fn apply(
                &mut self,
                _point: &Point,
                _body: &BlockBody,
            ) -> Result<(), LedgerError> {
                if !self.applied {
                    self.applied = true;
                    Err(LedgerError::new("first apply fails"))
                } else {
                    Ok(())
                }
            }
            async fn rollback(&mut self, _target: &Point) -> Result<(), LedgerError> {
                Ok(())
            }
            fn tip(&self) -> Option<Point> {
                None
            }
        }

        // Build the validator directly on LedgerOutcome so the test can
        // observe the failure without going through the ValidationComplete
        // shim (which drops failures).
        let (cmd_tx, cmd_rx) = mpsc::channel(8);
        let (outcome_tx, mut outcome_rx) = mpsc::channel(8);
        let dyn_rx = test_dyn_config(0.0, 0.0, 0.0);
        tokio::spawn(run_validator_actor(
            Box::new(FailFirstLedger { applied: false }),
            cmd_rx,
            outcome_tx,
            dyn_rx,
        ));

        cmd_tx
            .send(LedgerCommand::Apply {
                point: fake_point(1, 0x01),
                body: BlockBody::opaque(vec![]),
            })
            .await
            .unwrap();
        cmd_tx
            .send(LedgerCommand::Apply {
                point: fake_point(2, 0x02),
                body: BlockBody::opaque(vec![]),
            })
            .await
            .unwrap();

        match outcome_rx.recv().await.unwrap() {
            LedgerOutcome::ApplyFailed { point, error } => {
                assert_eq!(point, fake_point(1, 0x01));
                assert!(error.contains("first apply fails"));
            }
            other => panic!("expected ApplyFailed, got {other:?}"),
        }
        match outcome_rx.recv().await.unwrap() {
            LedgerOutcome::Applied { point } => {
                assert_eq!(point, fake_point(2, 0x02));
            }
            other => panic!("expected Applied, got {other:?}"),
        }
    }

    #[tokio::test]
    async fn eb_validate_returns_eb_validated() {
        let rx = test_dyn_config(0.0, 0.0, 0.0);
        let (validator, mut outcome_rx) = Validator::new(rx);

        let point = fake_point(50, 0xEB);
        validator
            .submit(LedgerCommand::ValidateEb {
                point: point.clone(),
            })
            .await;

        match outcome_rx.recv().await.expect("outcome") {
            LedgerOutcome::EbValidated { point: got } => assert_eq!(got, point),
            other => panic!("expected EbValidated, got {other:?}"),
        }
    }

    #[tokio::test]
    async fn votes_validate_returns_votes_validated() {
        let rx = test_dyn_config(0.0, 0.0, 0.0);
        let (validator, mut outcome_rx) = Validator::new(rx);

        let vote_ids = vec![(10u64, vec![0xAAu8]), (20u64, vec![0xBBu8])];
        let vote_data = vec![vec![0x01], vec![0x02]];
        validator
            .submit(LedgerCommand::ValidateVotes {
                vote_ids: vote_ids.clone(),
                vote_data: vote_data.clone(),
            })
            .await;

        match outcome_rx.recv().await.expect("outcome") {
            LedgerOutcome::VotesValidated {
                vote_ids: got_ids,
                vote_data: got_data,
            } => {
                assert_eq!(got_ids, vote_ids);
                assert_eq!(got_data, vote_data);
            }
            other => panic!("expected VotesValidated, got {other:?}"),
        }
    }
}
