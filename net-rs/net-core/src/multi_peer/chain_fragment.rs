//! Per-peer chain fragment tracking for fork-aware block fetch routing.
//!
//! Each peer announces headers via ChainSync. The `ChainFragment` records
//! the ordered sequence of points from intersection to tip, enabling the
//! coordinator to answer "does this peer have block X?" in O(1).

use std::collections::HashSet;

use crate::types::Point;

/// Tracks the chain fragment announced by a peer via ChainSync.
///
/// Built incrementally: `set_intersection` establishes the base, `append`
/// adds each announced header, `rollback_to` truncates on rollback.
/// The coordinator prunes fetched points via `remove`.
pub(crate) struct ChainFragment {
    /// Ordered list of announced points (intersection first, then headers).
    points: Vec<Point>,
    /// Set for O(1) lookup during fetch routing.
    point_set: HashSet<Point>,
}

impl ChainFragment {
    /// Create an empty fragment.
    pub fn new() -> Self {
        Self {
            points: Vec::new(),
            point_set: HashSet::new(),
        }
    }

    /// Reset the fragment to a single intersection point.
    /// Called when ChainSync completes `find_intersection`.
    pub fn set_intersection(&mut self, point: Point) {
        self.points.clear();
        self.point_set.clear();
        self.point_set.insert(point.clone());
        self.points.push(point);
    }

    /// Append a newly announced header's point.
    pub fn append(&mut self, point: Point) {
        if self.point_set.insert(point.clone()) {
            self.points.push(point);
        }
    }

    /// Truncate the fragment after a rollback to the given point.
    /// Keeps the rollback point and everything before it.
    /// If the point is not in the fragment, does nothing.
    pub fn rollback_to(&mut self, point: &Point) {
        if let Some(pos) = self.points.iter().position(|p| p == point) {
            // Remove everything after the rollback point.
            for removed in self.points.drain(pos + 1..) {
                self.point_set.remove(&removed);
            }
        }
    }

    /// Check whether this peer's fragment contains the given point.
    pub fn contains(&self, point: &Point) -> bool {
        self.point_set.contains(point)
    }

    /// Remove a specific point (e.g., after successful fetch or fetch failure).
    pub fn remove(&mut self, point: &Point) {
        if self.point_set.remove(point) {
            self.points.retain(|p| p != point);
        }
    }

    /// Number of points in the fragment.
    #[allow(dead_code)]
    pub fn len(&self) -> usize {
        self.points.len()
    }

    /// Whether the fragment is empty.
    #[allow(dead_code)]
    pub fn is_empty(&self) -> bool {
        self.points.is_empty()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn point(slot: u64) -> Point {
        Point::Specific {
            slot,
            hash: [slot as u8; 32],
        }
    }

    #[test]
    fn new_fragment_is_empty() {
        let f = ChainFragment::new();
        assert!(f.is_empty());
        assert_eq!(f.len(), 0);
        assert!(!f.contains(&point(1)));
    }

    #[test]
    fn set_intersection_resets_fragment() {
        let mut f = ChainFragment::new();
        f.append(point(1));
        f.append(point(2));
        assert_eq!(f.len(), 2);

        f.set_intersection(point(10));
        assert_eq!(f.len(), 1);
        assert!(f.contains(&point(10)));
        assert!(!f.contains(&point(1)));
        assert!(!f.contains(&point(2)));
    }

    #[test]
    fn append_and_contains() {
        let mut f = ChainFragment::new();
        f.set_intersection(point(100));
        f.append(point(101));
        f.append(point(102));
        f.append(point(103));

        assert_eq!(f.len(), 4);
        assert!(f.contains(&point(100)));
        assert!(f.contains(&point(101)));
        assert!(f.contains(&point(102)));
        assert!(f.contains(&point(103)));
        assert!(!f.contains(&point(99)));
        assert!(!f.contains(&point(104)));
    }

    #[test]
    fn append_deduplicates() {
        let mut f = ChainFragment::new();
        f.append(point(1));
        f.append(point(1));
        assert_eq!(f.len(), 1);
    }

    #[test]
    fn rollback_truncates_after_point() {
        let mut f = ChainFragment::new();
        f.set_intersection(point(100));
        f.append(point(101));
        f.append(point(102));
        f.append(point(103));

        f.rollback_to(&point(101));
        assert_eq!(f.len(), 2);
        assert!(f.contains(&point(100)));
        assert!(f.contains(&point(101)));
        assert!(!f.contains(&point(102)));
        assert!(!f.contains(&point(103)));
    }

    #[test]
    fn rollback_to_intersection_keeps_only_intersection() {
        let mut f = ChainFragment::new();
        f.set_intersection(point(100));
        f.append(point(101));
        f.append(point(102));

        f.rollback_to(&point(100));
        assert_eq!(f.len(), 1);
        assert!(f.contains(&point(100)));
    }

    #[test]
    fn rollback_to_unknown_point_is_noop() {
        let mut f = ChainFragment::new();
        f.set_intersection(point(100));
        f.append(point(101));

        f.rollback_to(&point(999));
        assert_eq!(f.len(), 2);
        assert!(f.contains(&point(100)));
        assert!(f.contains(&point(101)));
    }

    #[test]
    fn remove_specific_point() {
        let mut f = ChainFragment::new();
        f.set_intersection(point(100));
        f.append(point(101));
        f.append(point(102));

        f.remove(&point(101));
        assert_eq!(f.len(), 2);
        assert!(f.contains(&point(100)));
        assert!(!f.contains(&point(101)));
        assert!(f.contains(&point(102)));
    }

    #[test]
    fn remove_nonexistent_point_is_noop() {
        let mut f = ChainFragment::new();
        f.append(point(1));
        f.remove(&point(99));
        assert_eq!(f.len(), 1);
    }
}
