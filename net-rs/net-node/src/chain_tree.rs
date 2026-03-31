//! Tree of block headers for fork tracking and longest-chain selection.
//!
//! Maintains a tree of block headers keyed by hash. When a peer announces
//! a new block, it is inserted into the tree via its `prev_hash` link.
//! The longest chain (highest `block_number`) is selected as the best tip.
//! Blocks deeper than `k` below the best tip are pruned.

use std::collections::{HashMap, HashSet};

use net_core::types::Point;

/// A node in the chain tree, representing one block header.
#[derive(Debug, Clone)]
struct ChainNode {
    point: Point,
    block_number: u64,
    #[allow(dead_code)] // stored for future use (e.g., slot-based tiebreaking)
    slot: u64,
    prev_hash: Option<[u8; 32]>,
}

/// Tree of block headers for fork tracking and longest-chain selection.
///
/// Blocks are keyed by their 32-byte hash. The `best_tip` is cached and
/// updated on every insert. Pruning removes blocks deeper than `k` below
/// the best tip.
#[derive(Debug)]
pub struct ChainTree {
    nodes: HashMap<[u8; 32], ChainNode>,
    best_tip: Option<(Point, u64)>, // (point, block_number)
}

impl ChainTree {
    pub fn new() -> Self {
        Self {
            nodes: HashMap::new(),
            best_tip: None,
        }
    }

    /// Insert a block. Returns true if this block becomes the new best tip.
    pub fn insert(
        &mut self,
        hash: [u8; 32],
        point: Point,
        block_number: u64,
        slot: u64,
        prev_hash: Option<[u8; 32]>,
    ) -> bool {
        // Duplicate — no change.
        if self.nodes.contains_key(&hash) {
            return false;
        }

        self.nodes.insert(
            hash,
            ChainNode {
                point: point.clone(),
                block_number,
                slot,
                prev_hash,
            },
        );

        let is_new_best = match &self.best_tip {
            None => true,
            Some((_, best_bn)) => {
                if block_number != *best_bn {
                    block_number > *best_bn
                } else {
                    // Deterministic tie-breaker: lower hash wins.
                    let best_hash = self.best_tip_hash().unwrap_or([0xFF; 32]);
                    hash < best_hash
                }
            }
        };

        if is_new_best {
            self.best_tip = Some((point, block_number));
        }

        is_new_best
    }

    /// Check whether a block hash is in the tree.
    #[cfg(test)]
    pub fn contains(&self, hash: &[u8; 32]) -> bool {
        self.nodes.contains_key(hash)
    }

    /// The current best tip (highest block_number).
    pub fn best_tip(&self) -> Option<(&Point, u64)> {
        self.best_tip.as_ref().map(|(p, bn)| (p, *bn))
    }

    /// Extract the hash from the best tip's Point.
    pub fn best_tip_hash(&self) -> Option<[u8; 32]> {
        match &self.best_tip {
            Some((Point::Specific { hash, .. }, _)) => Some(*hash),
            _ => None,
        }
    }

    /// Look up block_number for a given hash.
    pub fn block_number(&self, hash: &[u8; 32]) -> Option<u64> {
        self.nodes.get(hash).map(|n| n.block_number)
    }

    /// Look up the point for a given hash.
    pub(crate) fn point(&self, hash: &[u8; 32]) -> Option<&Point> {
        self.nodes.get(hash).map(|n| &n.point)
    }

    /// Number of blocks in the tree.
    #[cfg(test)]
    pub fn len(&self) -> usize {
        self.nodes.len()
    }

    /// Prune blocks with block_number below the threshold.
    pub fn prune_below(&mut self, min_block_number: u64) {
        self.nodes
            .retain(|_, node| node.block_number >= min_block_number);
    }

    /// Walk the prev_hash chain from `hash` back to genesis (or a gap),
    /// collecting hashes in reverse order (tip first).
    pub(crate) fn ancestors(&self, mut hash: [u8; 32]) -> Vec<[u8; 32]> {
        let mut chain = vec![hash];
        while let Some(node) = self.nodes.get(&hash) {
            match node.prev_hash {
                Some(parent) if self.nodes.contains_key(&parent) => {
                    chain.push(parent);
                    hash = parent;
                }
                _ => break,
            }
        }
        chain
    }

    /// Find the common ancestor of two block hashes by walking both chains
    /// back until they meet. Returns the common ancestor hash, or None if
    /// the chains are disconnected (gap in the tree).
    pub fn find_common_ancestor(&self, hash_a: [u8; 32], hash_b: [u8; 32]) -> Option<[u8; 32]> {
        let ancestors_a: HashSet<[u8; 32]> = self.ancestors(hash_a).into_iter().collect();
        self.ancestors(hash_b)
            .into_iter()
            .find(|ancestor| ancestors_a.contains(ancestor))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn linear_chain() {
        let mut tree = ChainTree::new();

        assert!(tree.insert(
            [1; 32],
            Point::Specific {
                slot: 1,
                hash: [1; 32]
            },
            1,
            1,
            None
        ));
        assert!(tree.insert(
            [2; 32],
            Point::Specific {
                slot: 2,
                hash: [2; 32]
            },
            2,
            2,
            Some([1; 32])
        ));
        assert!(tree.insert(
            [3; 32],
            Point::Specific {
                slot: 3,
                hash: [3; 32]
            },
            3,
            3,
            Some([2; 32])
        ));

        let (_, bn) = tree.best_tip().unwrap();
        assert_eq!(bn, 3);
        assert_eq!(tree.len(), 3);
    }

    #[test]
    fn fork_longer_wins() {
        let mut tree = ChainTree::new();

        // Chain A: 3 blocks.
        tree.insert(
            [1; 32],
            Point::Specific {
                slot: 1,
                hash: [1; 32],
            },
            1,
            1,
            None,
        );
        tree.insert(
            [2; 32],
            Point::Specific {
                slot: 2,
                hash: [2; 32],
            },
            2,
            2,
            Some([1; 32]),
        );
        tree.insert(
            [3; 32],
            Point::Specific {
                slot: 3,
                hash: [3; 32],
            },
            3,
            3,
            Some([2; 32]),
        );

        // Chain B: fork from block 1, extends to 4.
        tree.insert(
            [0xB2; 32],
            Point::Specific {
                slot: 2,
                hash: [0xB2; 32],
            },
            2,
            2,
            Some([1; 32]),
        );
        tree.insert(
            [0xB3; 32],
            Point::Specific {
                slot: 3,
                hash: [0xB3; 32],
            },
            3,
            3,
            Some([0xB2; 32]),
        );
        let switched = tree.insert(
            [0xB4; 32],
            Point::Specific {
                slot: 4,
                hash: [0xB4; 32],
            },
            4,
            4,
            Some([0xB3; 32]),
        );

        assert!(switched, "chain B should become best");
        let (tip, bn) = tree.best_tip().unwrap();
        assert_eq!(bn, 4);
        assert_eq!(
            *tip,
            Point::Specific {
                slot: 4,
                hash: [0xB4; 32]
            }
        );
    }

    #[test]
    fn fork_shorter_ignored() {
        let mut tree = ChainTree::new();

        // Chain A: 3 blocks.
        tree.insert(
            [1; 32],
            Point::Specific {
                slot: 1,
                hash: [1; 32],
            },
            1,
            1,
            None,
        );
        tree.insert(
            [2; 32],
            Point::Specific {
                slot: 2,
                hash: [2; 32],
            },
            2,
            2,
            Some([1; 32]),
        );
        tree.insert(
            [3; 32],
            Point::Specific {
                slot: 3,
                hash: [3; 32],
            },
            3,
            3,
            Some([2; 32]),
        );

        // Chain B: fork from block 1, only 2 blocks total.
        let switched = tree.insert(
            [0xC2; 32],
            Point::Specific {
                slot: 2,
                hash: [0xC2; 32],
            },
            2,
            2,
            Some([1; 32]),
        );

        assert!(!switched, "shorter fork should not become best");
        let (_, bn) = tree.best_tip().unwrap();
        assert_eq!(bn, 3);
    }

    #[test]
    fn duplicate_ignored() {
        let mut tree = ChainTree::new();
        tree.insert(
            [1; 32],
            Point::Specific {
                slot: 1,
                hash: [1; 32],
            },
            1,
            1,
            None,
        );
        let dup = tree.insert(
            [1; 32],
            Point::Specific {
                slot: 1,
                hash: [1; 32],
            },
            1,
            1,
            None,
        );
        assert!(!dup);
        assert_eq!(tree.len(), 1);
    }

    #[test]
    fn tie_break_lower_hash_wins() {
        let mut tree = ChainTree::new();

        // Insert block with higher hash first.
        tree.insert(
            [0xBB; 32],
            Point::Specific {
                slot: 1,
                hash: [0xBB; 32],
            },
            1,
            1,
            None,
        );
        assert_eq!(tree.best_tip_hash(), Some([0xBB; 32]));

        // Insert block with same block_number but lower hash — should become best.
        let switched = tree.insert(
            [0xAA; 32],
            Point::Specific {
                slot: 1,
                hash: [0xAA; 32],
            },
            1,
            1,
            None,
        );
        assert!(switched, "lower hash should win tie");
        assert_eq!(tree.best_tip_hash(), Some([0xAA; 32]));

        // Insert block with same block_number but higher hash — should NOT switch.
        let not_switched = tree.insert(
            [0xCC; 32],
            Point::Specific {
                slot: 1,
                hash: [0xCC; 32],
            },
            1,
            1,
            None,
        );
        assert!(!not_switched, "higher hash should not win tie");
        assert_eq!(tree.best_tip_hash(), Some([0xAA; 32]));
    }

    #[test]
    fn pruning() {
        let mut tree = ChainTree::new();
        for i in 1..=10u64 {
            let hash = [i as u8; 32];
            let prev = if i > 1 {
                Some([(i - 1) as u8; 32])
            } else {
                None
            };
            tree.insert(hash, Point::Specific { slot: i, hash }, i, i, prev);
        }
        assert_eq!(tree.len(), 10);

        tree.prune_below(6);
        assert_eq!(tree.len(), 5); // blocks 6..=10
        assert!(!tree.contains(&[1; 32]));
        assert!(tree.contains(&[6; 32]));
        assert!(tree.contains(&[10; 32]));
    }

    #[test]
    fn common_ancestor_linear() {
        let mut tree = ChainTree::new();
        tree.insert(
            [1; 32],
            Point::Specific {
                slot: 1,
                hash: [1; 32],
            },
            1,
            1,
            None,
        );
        tree.insert(
            [2; 32],
            Point::Specific {
                slot: 2,
                hash: [2; 32],
            },
            2,
            2,
            Some([1; 32]),
        );
        tree.insert(
            [3; 32],
            Point::Specific {
                slot: 3,
                hash: [3; 32],
            },
            3,
            3,
            Some([2; 32]),
        );

        // Common ancestor of block 2 and block 3 is block 2.
        assert_eq!(tree.find_common_ancestor([2; 32], [3; 32]), Some([2; 32]));
        // Common ancestor of block 1 and block 3 is block 1.
        assert_eq!(tree.find_common_ancestor([1; 32], [3; 32]), Some([1; 32]));
    }

    #[test]
    fn common_ancestor_fork() {
        let mut tree = ChainTree::new();
        // Shared prefix: 1 -> 2
        tree.insert(
            [1; 32],
            Point::Specific {
                slot: 1,
                hash: [1; 32],
            },
            1,
            1,
            None,
        );
        tree.insert(
            [2; 32],
            Point::Specific {
                slot: 2,
                hash: [2; 32],
            },
            2,
            2,
            Some([1; 32]),
        );
        // Fork A: 2 -> A3
        tree.insert(
            [0xA3; 32],
            Point::Specific {
                slot: 3,
                hash: [0xA3; 32],
            },
            3,
            3,
            Some([2; 32]),
        );
        // Fork B: 2 -> B3 -> B4
        tree.insert(
            [0xB3; 32],
            Point::Specific {
                slot: 3,
                hash: [0xB3; 32],
            },
            3,
            3,
            Some([2; 32]),
        );
        tree.insert(
            [0xB4; 32],
            Point::Specific {
                slot: 4,
                hash: [0xB4; 32],
            },
            4,
            4,
            Some([0xB3; 32]),
        );

        // Common ancestor of A3 and B4 should be block 2.
        assert_eq!(
            tree.find_common_ancestor([0xA3; 32], [0xB4; 32]),
            Some([2; 32])
        );
    }
}
