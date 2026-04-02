//! Fake validation with configurable timed delays.
//!
//! Validation tasks are spawned as background tokio tasks that sleep for a
//! configured duration, then send a completion message back to the main loop.

use std::time::Duration;

use net_core::types::{BlockBody, Point};
use tokio::sync::{mpsc, watch};

use crate::config::DynamicConfig;

/// Result of a completed validation.
#[derive(Debug)]
pub struct ValidationComplete {
    /// The block point that was validated.
    pub point: Point,
}

/// Manages fake validation tasks.
pub struct Validator {
    dyn_config: watch::Receiver<DynamicConfig>,
    sender: mpsc::Sender<ValidationComplete>,
}

impl Validator {
    /// Create a new validator. Returns the validator and a receiver for
    /// completed validations.
    pub fn new(
        dyn_config: watch::Receiver<DynamicConfig>,
    ) -> (Self, mpsc::Receiver<ValidationComplete>) {
        let (sender, receiver) = mpsc::channel(64);
        (Self { dyn_config, sender }, receiver)
    }

    /// Submit a block for validation. Spawns a background task that sleeps
    /// for the configured duration, then sends a completion.
    pub fn validate_block(&self, point: Point, body: BlockBody) {
        let delay = self.block_validation_delay(body.raw.len());
        let sender = self.sender.clone();
        tokio::spawn(async move {
            tokio::time::sleep(delay).await;
            let _ = sender.send(ValidationComplete { point }).await;
        });
    }

    /// Compute the total validation delay for a block of the given size.
    fn block_validation_delay(&self, body_len: usize) -> Duration {
        let config = self.dyn_config.borrow();
        let ms = config.rb_head_validation_ms
            + config.rb_body_validation_ms_constant
            + config.rb_body_validation_ms_per_byte * body_len as f64;
        Duration::from_secs_f64(ms / 1000.0)
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

    #[test]
    fn delay_computation() {
        let rx = test_dyn_config(1.0, 5.0, 0.001);
        let (validator, _rx) = Validator::new(rx);

        // 1000-byte body: 1.0 + 5.0 + 0.001*1000 = 7.0ms
        let delay = validator.block_validation_delay(1000);
        let ms = delay.as_secs_f64() * 1000.0;
        assert!((ms - 7.0).abs() < 0.01, "delay was {ms}ms, expected 7.0ms");

        // 0-byte body: 1.0 + 5.0 + 0.0 = 6.0ms
        let delay = validator.block_validation_delay(0);
        let ms = delay.as_secs_f64() * 1000.0;
        assert!((ms - 6.0).abs() < 0.01, "delay was {ms}ms, expected 6.0ms");
    }

    #[tokio::test]
    async fn validate_block_completes() {
        let rx = test_dyn_config(0.0, 0.0, 0.0);
        let (validator, mut rx) = Validator::new(rx);

        let point = Point::Specific {
            slot: 42,
            hash: [0xAB; 32],
        };
        let body = BlockBody::opaque(vec![0u8; 100]);

        validator.validate_block(point.clone(), body);

        let result = rx.recv().await.expect("should receive completion");
        assert_eq!(result.point, point);
    }
}
