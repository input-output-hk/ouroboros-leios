//! Slot-granular delay queue.
//!
//! Behaviours wanting to hold an effect for N slots before releasing it
//! own a [`DelayQueue<E>`].  Pattern:
//!
//! ```ignore
//! impl Behaviour for MyDelayer {
//!     fn on_slot_leios(&mut self, _state: &LeiosState, slot: u64)
//!         -> BehaviourOutcome<LeiosEffect>
//!     {
//!         let drained = self.queue.drain_up_to(slot);
//!         if drained.is_empty() {
//!             BehaviourOutcome::Continue
//!         } else {
//!             BehaviourOutcome::Append(drained)
//!         }
//!     }
//!
//!     fn on_eb_offered(&mut self, _state: &LeiosState, point: &Point, peer: PeerId)
//!         -> BehaviourOutcome<LeiosEffect>
//!     {
//!         // Suppress immediate honest emission and queue for later.
//!         let honest = /* compute what honest would have emitted */;
//!         self.queue.push(slot + 2, honest);
//!         BehaviourOutcome::Replace(vec![])
//!     }
//! }
//! ```
//!
//! Granularity is one slot (~1 s).  Sub-slot delay is out of scope —
//! see the module docs for the design rationale.

use std::collections::BTreeMap;

/// Maps target slot → effects ready at that slot.  Entries are drained
/// when [`drain_up_to`](Self::drain_up_to) is called with a `slot >=
/// target`.  Multiple pushes to the same target slot are concatenated.
#[derive(Debug)]
pub struct DelayQueue<E> {
    by_slot: BTreeMap<u64, Vec<E>>,
}

impl<E> Default for DelayQueue<E> {
    fn default() -> Self {
        Self {
            by_slot: BTreeMap::new(),
        }
    }
}

impl<E> DelayQueue<E> {
    pub fn new() -> Self {
        Self::default()
    }

    /// Queue `effects` to be released at `target_slot`.  Multiple pushes
    /// to the same slot concatenate in insertion order.
    pub fn push(&mut self, target_slot: u64, effects: Vec<E>) {
        if effects.is_empty() {
            return;
        }
        self.by_slot.entry(target_slot).or_default().extend(effects);
    }

    /// Drain every effect whose `target_slot <= current_slot`.  Returned
    /// in (slot, push-order) order.
    pub fn drain_up_to(&mut self, current_slot: u64) -> Vec<E> {
        let mut out = Vec::new();
        let keys: Vec<u64> = self
            .by_slot
            .range(..=current_slot)
            .map(|(k, _)| *k)
            .collect();
        for k in keys {
            if let Some(mut v) = self.by_slot.remove(&k) {
                out.append(&mut v);
            }
        }
        out
    }

    pub fn is_empty(&self) -> bool {
        self.by_slot.is_empty()
    }

    pub fn pending(&self) -> usize {
        self.by_slot.values().map(|v| v.len()).sum()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn drain_returns_nothing_before_target() {
        let mut q: DelayQueue<u32> = DelayQueue::new();
        q.push(10, vec![1, 2, 3]);
        assert!(q.drain_up_to(9).is_empty());
        assert_eq!(q.pending(), 3);
    }

    #[test]
    fn drain_releases_at_target_slot() {
        let mut q: DelayQueue<u32> = DelayQueue::new();
        q.push(10, vec![1, 2, 3]);
        assert_eq!(q.drain_up_to(10), vec![1, 2, 3]);
        assert!(q.is_empty());
    }

    #[test]
    fn drain_releases_earlier_slots_too() {
        let mut q: DelayQueue<u32> = DelayQueue::new();
        q.push(5, vec![1]);
        q.push(7, vec![2]);
        q.push(9, vec![3]);
        // Calling at slot 8 releases slots 5 and 7 but not 9.
        assert_eq!(q.drain_up_to(8), vec![1, 2]);
        assert_eq!(q.pending(), 1);
        assert_eq!(q.drain_up_to(100), vec![3]);
    }

    #[test]
    fn same_slot_pushes_concat_in_order() {
        let mut q: DelayQueue<u32> = DelayQueue::new();
        q.push(10, vec![1, 2]);
        q.push(10, vec![3]);
        q.push(10, vec![4, 5]);
        assert_eq!(q.drain_up_to(10), vec![1, 2, 3, 4, 5]);
    }

    #[test]
    fn empty_push_does_nothing() {
        let mut q: DelayQueue<u32> = DelayQueue::new();
        q.push(10, vec![]);
        assert!(q.is_empty());
    }
}
