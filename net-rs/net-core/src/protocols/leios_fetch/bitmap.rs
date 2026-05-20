//! Helpers for the sparse `BTreeMap<u16, u64>` bitmap used by
//! `MsgLeiosBlockTxsRequest`.
//!
//! Per CIP-0164: each entry maps a 16-bit segment index to a 64-bit
//! mask, and the offset of the mask's first bit is `64 * segment`.
//! Transaction `i` is requested iff bit `i % 64` of `bitmap[i / 64]`
//! is set.
//!
//! An empty bitmap selects no transactions. To request all `n` txs
//! use `select_all(n)`.

use std::collections::BTreeMap;

/// Bit `i` of the segment mask corresponds to absolute index `64*seg + i`.
const SEGMENT_BITS: u32 = 64;

/// Build a sparse bitmap with the given indices set.
pub fn from_indices(indices: &[u32]) -> BTreeMap<u16, u64> {
    let mut bitmap: BTreeMap<u16, u64> = BTreeMap::new();
    for &index in indices {
        let segment = (index / SEGMENT_BITS) as u16;
        let bit = index % SEGMENT_BITS;
        let entry = bitmap.entry(segment).or_insert(0);
        *entry |= 1u64 << bit;
    }
    bitmap
}

/// Build a bitmap with indices `0..count` set (every tx selected).
pub fn select_all(count: u32) -> BTreeMap<u16, u64> {
    let mut bitmap: BTreeMap<u16, u64> = BTreeMap::new();
    let full_segments = count / SEGMENT_BITS;
    let remainder = count % SEGMENT_BITS;
    for seg in 0..full_segments {
        bitmap.insert(seg as u16, u64::MAX);
    }
    if remainder > 0 {
        let mask = (1u64 << remainder) - 1;
        bitmap.insert(full_segments as u16, mask);
    }
    bitmap
}

/// True iff `index` is selected by the bitmap.
pub fn contains(bitmap: &BTreeMap<u16, u64>, index: u32) -> bool {
    let segment = (index / SEGMENT_BITS) as u16;
    let bit = index % SEGMENT_BITS;
    bitmap
        .get(&segment)
        .map(|mask| mask & (1u64 << bit) != 0)
        .unwrap_or(false)
}

/// Iterate the set indices in ascending order.
pub fn iter_indices(bitmap: &BTreeMap<u16, u64>) -> impl Iterator<Item = u32> + '_ {
    bitmap.iter().flat_map(|(&segment, &mask)| {
        let base = segment as u32 * SEGMENT_BITS;
        (0..SEGMENT_BITS).filter_map(move |bit| {
            if mask & (1u64 << bit) != 0 {
                Some(base + bit)
            } else {
                None
            }
        })
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn from_indices_packs_bits_into_segments() {
        let bitmap = from_indices(&[0, 1, 63, 64, 65, 200]);
        // 0,1,63 → segment 0
        assert_eq!(bitmap[&0], (1u64 << 0) | (1u64 << 1) | (1u64 << 63));
        // 64,65 → segment 1
        assert_eq!(bitmap[&1], (1u64 << 0) | (1u64 << 1));
        // 200 → segment 3, bit 8
        assert_eq!(bitmap[&3], 1u64 << 8);
        assert_eq!(bitmap.len(), 3);
    }

    #[test]
    fn from_indices_empty_input_empty_bitmap() {
        assert!(from_indices(&[]).is_empty());
    }

    #[test]
    fn from_indices_duplicate_index_is_idempotent() {
        let a = from_indices(&[5, 5, 5]);
        let b = from_indices(&[5]);
        assert_eq!(a, b);
    }

    #[test]
    fn select_all_zero_is_empty() {
        assert!(select_all(0).is_empty());
    }

    #[test]
    fn select_all_partial_segment_uses_low_bits() {
        let bitmap = select_all(3);
        assert_eq!(bitmap.len(), 1);
        assert_eq!(bitmap[&0], 0b111);
    }

    #[test]
    fn select_all_exact_segment_boundary() {
        let bitmap = select_all(64);
        assert_eq!(bitmap.len(), 1);
        assert_eq!(bitmap[&0], u64::MAX);
    }

    #[test]
    fn select_all_multi_segment() {
        let bitmap = select_all(130);
        assert_eq!(bitmap.len(), 3);
        assert_eq!(bitmap[&0], u64::MAX);
        assert_eq!(bitmap[&1], u64::MAX);
        assert_eq!(bitmap[&2], 0b11);
    }

    #[test]
    fn contains_matches_selection() {
        let bitmap = from_indices(&[0, 63, 64, 200]);
        assert!(contains(&bitmap, 0));
        assert!(contains(&bitmap, 63));
        assert!(contains(&bitmap, 64));
        assert!(contains(&bitmap, 200));
        assert!(!contains(&bitmap, 1));
        assert!(!contains(&bitmap, 65));
        assert!(!contains(&bitmap, 199));
        assert!(!contains(&bitmap, 1000));
    }

    #[test]
    fn iter_indices_returns_indices_in_order() {
        let inputs = vec![200u32, 1, 64, 0, 63, 65];
        let bitmap = from_indices(&inputs);
        let collected: Vec<u32> = iter_indices(&bitmap).collect();
        assert_eq!(collected, vec![0, 1, 63, 64, 65, 200]);
    }

    #[test]
    fn iter_indices_round_trips_through_from_indices() {
        let original: Vec<u32> = (0..150).filter(|i| i % 7 == 0).collect();
        let bitmap = from_indices(&original);
        let recovered: Vec<u32> = iter_indices(&bitmap).collect();
        assert_eq!(recovered, original);
    }

    #[test]
    fn select_all_then_iter_yields_all() {
        let bitmap = select_all(70);
        let collected: Vec<u32> = iter_indices(&bitmap).collect();
        let expected: Vec<u32> = (0..70).collect();
        assert_eq!(collected, expected);
    }

    #[test]
    fn empty_bitmap_iterates_to_nothing() {
        let bitmap: BTreeMap<u16, u64> = BTreeMap::new();
        assert_eq!(iter_indices(&bitmap).count(), 0);
    }
}
