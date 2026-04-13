//! Validation handling: submit_for_validation, handle_applied,
//! handle_rolled_back, handle_apply_failed, on_block_received,
//! on_validation_outcome.

use net_core::multi_peer::types::NetworkCommand;
use net_core::types::{BlockBody, Point, WrappedHeader};
use tracing::info;

use crate::validation::{LedgerCommand, LedgerOutcome};

use super::CachedBlock;

impl super::PraosConsensus {
    /// Handle one outcome from the validator actor.
    ///
    /// Returns `true` if the chain_store rolled back as a result (so the
    /// telemetry layer can record the rollback event).
    pub async fn on_validation_outcome(&mut self, outcome: LedgerOutcome) -> bool {
        match outcome {
            LedgerOutcome::Applied { point } => {
                self.handle_applied(point).await;
                false
            }
            LedgerOutcome::RolledBack { target } => {
                self.handle_rolled_back(target).await;
                true
            }
            LedgerOutcome::ApplyFailed { point, error } => {
                self.handle_apply_failed(point, error);
                false
            }
            LedgerOutcome::RollbackFailed { target, error } => {
                tracing::error!(
                    node_id = %self.node_id,
                    %target,
                    %error,
                    "ledger rollback failed; consensus state may be inconsistent"
                );
                false
            }
            LedgerOutcome::EbValidated { .. } | LedgerOutcome::VotesValidated { .. } => {
                // Leios outcomes are handled by the facade before reaching Praos.
                false
            }
        }
    }

    /// Apply succeeded: publish the block to the chain_store, update the
    /// last-validated tip, prune below k, and re-run `select_chain` so any
    /// peer chain that became actionable while we were validating gets
    /// picked up.
    pub(super) async fn handle_applied(&mut self, point: Point) {
        let hash = match &point {
            Point::Specific { hash, .. } => *hash,
            _ => return,
        };
        self.in_flight.remove(&point);
        self.in_flight_validation.remove(&hash);

        let inject = match self.block_cache.get(&hash) {
            Some(cb) => NetworkCommand::InjectBlock {
                point: cb.point.clone(),
                header: Box::new(cb.header.clone()),
                body: cb.body.clone(),
                block_no: cb.block_no,
            },
            None => {
                tracing::warn!(
                    node_id = %self.node_id,
                    %point,
                    "applied outcome for block not in cache — ignoring"
                );
                return;
            }
        };
        self.validated.insert(hash);
        self.last_validated_tip = Some(hash);

        info!(
            node_id = %self.node_id,
            %point,
            "block validated, publishing to chain store"
        );
        let _ = self.commands.send(inject).await;

        // Prune old blocks beyond k.
        if let Some(adopted) = self.adopted_tip_hash {
            if let Some(bn) = self.chain_tree.block_number(&adopted) {
                if bn > self.security_param_k {
                    let min = bn - self.security_param_k;
                    self.chain_tree.prune_below(min);
                    self.block_cache.retain(|_, cb| cb.block_no >= min);
                    self.validated.retain(|h| self.block_cache.contains_key(h));
                }
            }
        }

        // Adopted tip advanced — try switching to chain_tree's best tip
        // (new chains may now be reachable), then fetch missing blocks.
        if let Some(best) = self.chain_tree.best_tip_hash() {
            self.try_switch_and_execute(best).await;
        }
        self.evaluate_and_fetch().await;
    }

    /// Rollback succeeded: the ledger is now back at `target`, so the
    /// chain store should mirror that.
    pub(super) async fn handle_rolled_back(&mut self, target: Point) {
        if target == Point::Origin {
            self.last_validated_tip = None;
            info!(
                node_id = %self.node_id,
                "ledger rolled back to Origin, clearing chain store"
            );
            let _ = self
                .commands
                .send(NetworkCommand::InjectRollback {
                    point: Point::Origin,
                })
                .await;
            return;
        }
        let hash = match &target {
            Point::Specific { hash, .. } => *hash,
            _ => return,
        };
        self.last_validated_tip = Some(hash);
        info!(
            node_id = %self.node_id,
            %target,
            "ledger rolled back, rolling chain store"
        );
        let _ = self
            .commands
            .send(NetworkCommand::InjectRollback { point: target })
            .await;
    }

    /// Apply failed: the block (and any cascade behind it) is no longer
    /// in the validator's accepted state. Rewind `queued_validator_tip`
    /// and `adopted_tip_hash` so the next submission realigns with what
    /// the ledger has actually accepted, and drop any children waiting
    /// on the failed block.
    pub(super) fn handle_apply_failed(&mut self, point: Point, error: String) {
        let hash = match &point {
            Point::Specific { hash, .. } => *hash,
            _ => return,
        };
        self.in_flight.remove(&point);
        self.in_flight_validation.remove(&hash);
        tracing::warn!(
            node_id = %self.node_id,
            %point,
            %error,
            "ledger apply failed; rewinding to last validated tip"
        );
        // The queue is no longer aimed at the failed block. Rewind to
        // whatever the last successfully-applied tip was; subsequent
        // submissions will issue a Rollback if needed to realign.
        self.queued_validator_tip = self.last_validated_tip;
        self.adopted_tip_hash = self.last_validated_tip;
        // The failed block stays in the cache but is no longer marked
        // validated. select_chain may pick a different candidate.
        self.validated.remove(&hash);
    }

    /// Submit a block for validation. Issues a `LedgerCommand::Apply`,
    /// preceded by a `Rollback` if the validator queue isn't currently
    /// aimed at the block's parent. Updates `queued_validator_tip` and
    /// `adopted_tip_hash` eagerly so subsequent decisions see the
    /// post-submission view.
    pub(super) async fn submit_for_validation(
        &mut self,
        point: Point,
        body: BlockBody,
        prev_hash: Option<[u8; 32]>,
    ) {
        let new_hash = match &point {
            Point::Specific { hash, .. } => *hash,
            _ => return,
        };

        // If the validator queue isn't currently aimed at this block's
        // parent, queue a Rollback first so the ledger ends up in the
        // right state for the apply.
        if prev_hash != self.queued_validator_tip {
            if let Some(parent_hash) = prev_hash {
                if let Some(parent_point) = self.chain_tree.point(&parent_hash).cloned() {
                    self.validator
                        .submit(LedgerCommand::Rollback {
                            target: parent_point,
                        })
                        .await;
                    self.queued_validator_tip = Some(parent_hash);
                } else {
                    let hex = |h: &[u8; 32]| format!("{:02x}{:02x}", h[30], h[31]);
                    tracing::debug!(
                        node_id = %self.node_id,
                        parent = hex(&parent_hash),
                        queued_tip = self.queued_validator_tip.as_ref().map(|h| format!("{:02x}{:02x}", h[30], h[31])).as_deref().unwrap_or("<none>"),
                        block = format!("{}", point),
                        "parent not in chain_tree — skipping rollback"
                    );
                }
            }
        }

        self.validator
            .submit(LedgerCommand::Apply {
                point: point.clone(),
                body,
            })
            .await;
        self.queued_validator_tip = Some(new_hash);
        self.adopted_tip_hash = Some(new_hash);
        self.in_flight_validation.insert(new_hash);
    }

    /// A fetched block arrived — cache it and run chain selection.
    /// Validation is driven by `select_chain` -> `execute_switch`.
    pub(super) async fn on_block_received(&mut self, point: &Point, body: &BlockBody) {
        let hash = match point {
            Point::Specific { hash, .. } => *hash,
            _ => return,
        };
        // Dedup: skip if already known to the validator or waiting on
        // its parent. `block_cache` covers the "already cached" case;
        // the other checks are belt-and-braces.
        if self.block_cache.contains_key(&hash)
            || self.validated.contains(&hash)
            || self.in_flight_validation.contains(&hash)
        {
            return;
        }
        let header = body
            .header()
            .unwrap_or_else(|| WrappedHeader::opaque(Vec::new()));
        let block_no = header
            .parsed
            .as_ref()
            .map(|i| i.block_number)
            .or_else(|| self.chain_tree.block_number(&hash))
            .unwrap_or(0);
        let prev_hash = header
            .parsed
            .as_ref()
            .and_then(|i| i.prev_hash)
            .or_else(|| self.chain_tree.prev_hash(&hash));
        // Insert into chain_tree so ancestors() can walk through fetched
        // blocks — critical for the adopted-chain ancestry lookup in
        // select_chain.
        if let Some(info) = header.parsed.as_ref() {
            self.chain_tree.insert(
                hash,
                point.clone(),
                info.block_number,
                info.slot,
                info.prev_hash,
            );
        } else if block_no > 0 {
            // Opaque header — insert with fallback metadata to avoid gaps
            // in chain_tree that break ancestors() walks. block_no and
            // prev_hash were derived from chain_tree lookups above; guard
            // block_no > 0 to avoid inserting with the default which would
            // confuse pruning and best_tip selection.
            let slot = match point {
                Point::Specific { slot, .. } => *slot,
                _ => 0,
            };
            self.chain_tree
                .insert(hash, point.clone(), block_no, slot, prev_hash);
        }
        self.block_cache.insert(
            hash,
            CachedBlock {
                point: point.clone(),
                header,
                body: body.clone(),
                block_no,
                prev_hash,
            },
        );

        info!(
            node_id = %self.node_id,
            %point,
            block_no,
            "block received and cached"
        );
        // Try switching to this specific block — no peer chain needed.
        self.try_switch_and_execute(hash).await;
    }
}
