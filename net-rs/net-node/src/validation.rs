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
//!
//! Consensus currently still consumes a `ValidationComplete { point }`
//! shim rather than `LedgerOutcome` directly; the shim exists only so
//! the validator can be refactored without churning the consensus layer
//! at the same time, and goes away once consensus wires up rollback and
//! failure outcomes.

use std::fmt;
use std::time::Duration;

use async_trait::async_trait;
use net_core::types::{BlockBody, Point};
use tokio::sync::{mpsc, watch};
use tracing::warn;

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
    #[allow(dead_code)] // consensus wires rollbacks in a follow-up commit
    Rollback { target: Point },
}

/// Outcomes reported by the validator actor after processing a command.
#[derive(Debug, Clone)]
#[allow(dead_code)] // rollback/failure variants consumed once consensus reacts to them
pub enum LedgerOutcome {
    /// `apply` succeeded for `point`.
    Applied { point: Point },
    /// `rollback` succeeded to `target`.
    RolledBack { target: Point },
    /// `apply` failed for `point`.
    ApplyFailed { point: Point, error: String },
    /// `rollback` failed for `target`.
    RollbackFailed { target: Point, error: String },
}

/// Result of a completed block validation.
///
/// Temporary shim carrying only the validated point so the consensus
/// layer's existing `on_validation_complete(ValidationComplete)` entry
/// point keeps working while the validator is refactored. Delete when
/// consensus consumes `LedgerOutcome` directly.
#[derive(Debug)]
pub struct ValidationComplete {
    /// The block point that was validated.
    pub point: Point,
}

/// Handle to the validator actor. Submitting work goes through this;
/// completion outcomes come back via the receiver returned from `new`.
pub struct Validator {
    commands: mpsc::Sender<LedgerCommand>,
}

impl Validator {
    /// Create a new validator with the default `FakeLedger` backend.
    /// Returns the handle and a receiver for completed validations.
    pub fn new(
        dyn_config: watch::Receiver<DynamicConfig>,
    ) -> (Self, mpsc::Receiver<ValidationComplete>) {
        let ledger = Box::new(FakeLedger::new(dyn_config));
        Self::with_ledger(ledger)
    }

    /// Create a validator with a caller-supplied ledger. Used by tests
    /// and by future real-ledger wiring.
    pub fn with_ledger(ledger: Box<dyn Ledger>) -> (Self, mpsc::Receiver<ValidationComplete>) {
        // Bounded channels give natural backpressure: if consensus
        // submits commands faster than the ledger can process them,
        // `send().await` blocks. 64 is enough for typical per-node
        // pipelines without being so deep that a stuck ledger
        // accumulates arbitrary work.
        let (cmd_tx, cmd_rx) = mpsc::channel(64);
        let (outcome_tx, outcome_rx) = mpsc::channel(64);
        tokio::spawn(run_validator_actor(ledger, cmd_rx, outcome_tx));

        let (shim_tx, shim_rx) = mpsc::channel(64);
        tokio::spawn(run_outcome_shim(outcome_rx, shim_tx));

        (Self { commands: cmd_tx }, shim_rx)
    }

    /// Submit a block for validation. Sends a `LedgerCommand::Apply`
    /// to the actor. Backpressure is applied by the bounded command
    /// channel; if it fills, this blocks until the actor drains it.
    ///
    /// Kept on the `(point, body)` signature to match consensus's
    /// current call sites; a direct `LedgerCommand` submission path
    /// replaces it once consensus handles the full outcome set.
    pub fn validate_block(&self, point: Point, body: BlockBody) {
        let tx = self.commands.clone();
        tokio::spawn(async move {
            let _ = tx.send(LedgerCommand::Apply { point, body }).await;
        });
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
        };
        if outcomes.send(outcome).await.is_err() {
            // Receiver dropped — consensus tore down. Exit cleanly.
            return;
        }
    }
}

/// Temporary bridge between `LedgerOutcome` (emitted by the actor) and
/// `ValidationComplete` (consumed by consensus). Delete when consensus
/// consumes `LedgerOutcome` directly.
async fn run_outcome_shim(
    mut outcomes: mpsc::Receiver<LedgerOutcome>,
    shim: mpsc::Sender<ValidationComplete>,
) {
    while let Some(outcome) = outcomes.recv().await {
        match outcome {
            LedgerOutcome::Applied { point } => {
                if shim.send(ValidationComplete { point }).await.is_err() {
                    return;
                }
            }
            LedgerOutcome::ApplyFailed { point, error } => {
                warn!(%point, %error, "ledger apply failed; consensus will retry on next tip advance");
            }
            LedgerOutcome::RolledBack { .. } | LedgerOutcome::RollbackFailed { .. } => {
                // No caller currently issues `Rollback` commands, so
                // these are unreachable in practice. They'll be wired
                // into consensus once it drives ledger rollbacks on
                // fork switch.
            }
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
    async fn validate_block_completes() {
        let rx = test_dyn_config(0.0, 0.0, 0.0);
        let (validator, mut rx) = Validator::new(rx);

        let point = fake_point(42, 0xAB);
        let body = BlockBody::opaque(vec![0u8; 100]);

        validator.validate_block(point.clone(), body);

        let result = rx.recv().await.expect("should receive completion");
        assert_eq!(result.point, point);
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

        validator.validate_block(p1.clone(), BlockBody::opaque(vec![]));
        validator.validate_block(p2.clone(), BlockBody::opaque(vec![]));
        validator.validate_block(p3.clone(), BlockBody::opaque(vec![]));

        // submit-spawned tasks land in the channel in submission order
        // because tokio::spawn + bounded send preserves it. Give them
        // a moment to drain.
        let r1 = outcome_rx.recv().await.unwrap();
        let r2 = outcome_rx.recv().await.unwrap();
        let r3 = outcome_rx.recv().await.unwrap();
        assert_eq!(r1.point, p1);
        assert_eq!(r2.point, p2);
        assert_eq!(r3.point, p3);
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
        tokio::spawn(run_validator_actor(
            Box::new(FailFirstLedger { applied: false }),
            cmd_rx,
            outcome_tx,
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
}
