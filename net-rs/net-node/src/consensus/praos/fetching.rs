//! Block fetching: issue_fetch, evict_stale_in_flight, mark_in_flight,
//! retry_select_chain.

use std::time::Instant;

use net_core::multi_peer::types::NetworkCommand;
use net_core::peer::PeerId;
use net_core::types::Point;
use tracing::info;

use super::IN_FLIGHT_TTL;

impl super::PraosConsensus {
    /// Issue a `FetchBlockRange` covering the missing replay blocks,
    /// skipping blocks already in flight.
    ///
    /// When `anchor_point` is set, the range starts from the anchor
    /// (ChainSync intersection) instead of the first missing entry.
    /// This fills the gap between the anchor and the oldest PeerChain
    /// entry — blocks that aren't in the PeerChain but are needed for
    /// the chain to be contiguous from the common ancestor to the tip.
    pub(super) async fn issue_fetch(
        &mut self,
        missing: Vec<Point>,
        anchor_point: Option<Point>,
        peer_id: Option<PeerId>,
    ) {
        if missing.is_empty() {
            return;
        }
        self.evict_stale_in_flight();

        // Single range from oldest to newest missing block. When the
        // anchor provided the common ancestor and there's a gap, use
        // the anchor as `from` so BlockFetch fills the gap.
        let from = anchor_point.unwrap_or_else(|| missing.first().unwrap().clone());
        let to = missing.last().unwrap().clone();
        if self.in_flight.contains_key(&to) {
            return;
        }
        self.mark_in_flight(to.clone());
        info!(
            node_id = %self.node_id,
            %from,
            %to,
            "fetching missing chain blocks"
        );
        let _ = self
            .commands
            .send(NetworkCommand::FetchBlockRange { from, to, peer_id })
            .await;
    }

    /// Drop stale `in_flight` entries (older than `IN_FLIGHT_TTL`). Called
    /// at the start of fetch-issuing flows so a silently-dropped fetch can
    /// be retried.
    pub(super) fn evict_stale_in_flight(&mut self) {
        let now = Instant::now();
        self.in_flight
            .retain(|_, started| now.duration_since(*started) < IN_FLIGHT_TTL);
    }

    pub(super) fn mark_in_flight(&mut self, point: Point) {
        self.in_flight.insert(point, Instant::now());
    }

    /// Periodic retry: evict stale in-flight entries and re-run chain
    /// selection. Called from the slot tick in the main loop to ensure
    /// lagging nodes retry fetches even when no new network events arrive
    /// (e.g., after block production stops).
    pub async fn retry_select_chain(&mut self) {
        let before = self.in_flight.len();
        self.evict_stale_in_flight();
        let evicted = before - self.in_flight.len();

        // Try switching using stored blocks first.
        if let Some(best) = self.chain_tree.best_tip_hash() {
            self.try_switch_and_execute(best).await;
        }

        if evicted > 0 || !self.in_flight.is_empty() {
            self.evaluate_and_fetch().await;
        }

        // If chain_tree has a gap between best_tip and adopted, fetch
        // the missing blocks. Done here (periodic) to avoid fetch storms.
        if let Some(best) = self.chain_tree.best_tip_hash() {
            if let Err(Some(gap_point)) = self.try_switch_to(best) {
                let from = self
                    .adopted_tip_hash
                    .and_then(|h| self.chain_tree.point(&h).cloned())
                    .unwrap_or(Point::Origin);
                let from_slot = match &from {
                    Point::Specific { slot, .. } => *slot,
                    _ => 0,
                };
                let to_slot = match &gap_point {
                    Point::Specific { slot, .. } => *slot,
                    _ => 0,
                };
                if to_slot > from_slot && !self.in_flight.contains_key(&gap_point) {
                    info!(
                        node_id = %self.node_id,
                        %from,
                        to = %gap_point,
                        "retry: fetching gap to bridge chain_tree"
                    );
                    self.mark_in_flight(gap_point.clone());
                    let _ = self
                        .commands
                        .send(NetworkCommand::FetchBlockRange {
                            from,
                            to: gap_point,
                            peer_id: None,
                        })
                        .await;
                }
            }
        }
    }
}
