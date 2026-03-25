//! CBOR encoding for LeiosFetch messages.
//!
//! Wire format:
//!   msgLeiosBlockRequest           = [0, slot, hash32]
//!   msgLeiosBlock                  = [1, block]
//!   msgLeiosBlockTxsRequest        = [2, slot, hash32, { u16 => u64, ... }]
//!   msgLeiosBlockTxs               = [3, [tx, ...]]
//!   msgLeiosVotesRequest           = [4, [(slot, voterId), ...]]
//!   msgLeiosVoteDelivery           = [5, [vote, ...]]
//!   msgLeiosBlockRangeRequest      = [6, startSlot, endSlot, startHash, endHash]
//!   msgLeiosNextBlockAndTxsInRange = [7, block, [tx, ...]]
//!   msgLeiosLastBlockAndTxsInRange = [8, block, [tx, ...]]
//!   msgDone                        = [9]

use std::collections::BTreeMap;

use minicbor::decode::Error as DecodeError;
use minicbor::encode::Error as EncodeError;
use minicbor::{Decoder, Encoder};

use super::{
    Message, MAX_BITMAP_ENTRIES, MAX_BLOCK_SIZE, MAX_TRANSACTIONS, MAX_TRANSACTION_SIZE,
    MAX_VOTER_ID_SIZE, MAX_VOTES, MAX_VOTE_SIZE,
};

impl minicbor::Encode<()> for Message {
    fn encode<W: minicbor::encode::Write>(
        &self,
        e: &mut Encoder<W>,
        _ctx: &mut (),
    ) -> Result<(), EncodeError<W::Error>> {
        match self {
            Message::MsgLeiosBlockRequest { slot, hash } => {
                e.array(3)?;
                e.u32(0)?;
                e.u64(*slot)?;
                e.bytes(hash)?;
            }
            Message::MsgLeiosBlock { block } => {
                e.array(2)?;
                e.u32(1)?;
                e.bytes(block)?;
            }
            Message::MsgLeiosBlockTxsRequest { slot, hash, bitmap } => {
                e.array(4)?;
                e.u32(2)?;
                e.u64(*slot)?;
                e.bytes(hash)?;
                encode_bitmap(e, bitmap)?;
            }
            Message::MsgLeiosBlockTxs { transactions } => {
                e.array(2)?;
                e.u32(3)?;
                encode_blob_list(e, transactions)?;
            }
            Message::MsgLeiosVotesRequest { votes } => {
                e.array(2)?;
                e.u32(4)?;
                e.array(votes.len() as u64)?;
                for (slot, voter_id) in votes {
                    e.array(2)?;
                    e.u64(*slot)?;
                    e.bytes(voter_id)?;
                }
            }
            Message::MsgLeiosVoteDelivery { votes } => {
                e.array(2)?;
                e.u32(5)?;
                encode_blob_list(e, votes)?;
            }
            Message::MsgLeiosBlockRangeRequest {
                start_slot,
                end_slot,
                start_hash,
                end_hash,
            } => {
                e.array(5)?;
                e.u32(6)?;
                e.u64(*start_slot)?;
                e.u64(*end_slot)?;
                e.bytes(start_hash)?;
                e.bytes(end_hash)?;
            }
            Message::MsgLeiosNextBlockAndTxsInRange {
                block,
                transactions,
            } => {
                e.array(3)?;
                e.u32(7)?;
                e.bytes(block)?;
                encode_blob_list(e, transactions)?;
            }
            Message::MsgLeiosLastBlockAndTxsInRange {
                block,
                transactions,
            } => {
                e.array(3)?;
                e.u32(8)?;
                e.bytes(block)?;
                encode_blob_list(e, transactions)?;
            }
            Message::MsgDone => {
                e.array(1)?;
                e.u32(9)?;
            }
        }
        Ok(())
    }
}

impl<'a> minicbor::Decode<'a, ()> for Message {
    fn decode(d: &mut Decoder<'a>, _ctx: &mut ()) -> Result<Self, DecodeError> {
        let _array_len = d.array()?;
        let tag = d.u32()?;

        match tag {
            0 => {
                let slot = d.u64()?;
                let hash = decode_hash32(d)?;
                Ok(Message::MsgLeiosBlockRequest { slot, hash })
            }
            1 => {
                let block = decode_block(d)?;
                Ok(Message::MsgLeiosBlock { block })
            }
            2 => {
                let slot = d.u64()?;
                let hash = decode_hash32(d)?;
                let bitmap = decode_bitmap(d)?;
                Ok(Message::MsgLeiosBlockTxsRequest { slot, hash, bitmap })
            }
            3 => {
                let transactions =
                    decode_blob_list(d, MAX_TRANSACTIONS, MAX_TRANSACTION_SIZE, "transaction")?;
                Ok(Message::MsgLeiosBlockTxs { transactions })
            }
            4 => {
                let votes = decode_vote_id_list(d)?;
                Ok(Message::MsgLeiosVotesRequest { votes })
            }
            5 => {
                let votes = decode_blob_list(d, MAX_VOTES, MAX_VOTE_SIZE, "vote")?;
                Ok(Message::MsgLeiosVoteDelivery { votes })
            }
            6 => {
                let start_slot = d.u64()?;
                let end_slot = d.u64()?;
                let start_hash = decode_hash32(d)?;
                let end_hash = decode_hash32(d)?;
                Ok(Message::MsgLeiosBlockRangeRequest {
                    start_slot,
                    end_slot,
                    start_hash,
                    end_hash,
                })
            }
            7 => {
                let block = decode_block(d)?;
                let transactions =
                    decode_blob_list(d, MAX_TRANSACTIONS, MAX_TRANSACTION_SIZE, "transaction")?;
                Ok(Message::MsgLeiosNextBlockAndTxsInRange {
                    block,
                    transactions,
                })
            }
            8 => {
                let block = decode_block(d)?;
                let transactions =
                    decode_blob_list(d, MAX_TRANSACTIONS, MAX_TRANSACTION_SIZE, "transaction")?;
                Ok(Message::MsgLeiosLastBlockAndTxsInRange {
                    block,
                    transactions,
                })
            }
            9 => Ok(Message::MsgDone),
            other => Err(DecodeError::message(format!(
                "unknown leios_fetch message tag: {other}"
            ))),
        }
    }
}

// --- Encode helpers ---

fn encode_bitmap<W: minicbor::encode::Write>(
    e: &mut Encoder<W>,
    bitmap: &BTreeMap<u16, u64>,
) -> Result<(), EncodeError<W::Error>> {
    e.map(bitmap.len() as u64)?;
    for (index, bits) in bitmap {
        e.u16(*index)?;
        e.u64(*bits)?;
    }
    Ok(())
}

fn encode_blob_list<W: minicbor::encode::Write>(
    e: &mut Encoder<W>,
    blobs: &[Vec<u8>],
) -> Result<(), EncodeError<W::Error>> {
    e.array(blobs.len() as u64)?;
    for blob in blobs {
        e.bytes(blob)?;
    }
    Ok(())
}

// --- Decode helpers ---

/// Decode a 32-byte hash from CBOR bytes.
fn decode_hash32(d: &mut Decoder<'_>) -> Result<[u8; 32], DecodeError> {
    let bytes = d.bytes()?;
    if bytes.len() != 32 {
        return Err(DecodeError::message(format!(
            "expected 32-byte hash, got {} bytes",
            bytes.len()
        )));
    }
    let mut hash = [0u8; 32];
    hash.copy_from_slice(bytes);
    Ok(hash)
}

/// Decode an opaque block blob with size limit.
fn decode_block(d: &mut Decoder<'_>) -> Result<Vec<u8>, DecodeError> {
    let bytes = d.bytes()?;
    if bytes.len() > MAX_BLOCK_SIZE {
        return Err(DecodeError::message(format!(
            "block is {} bytes, maximum is {MAX_BLOCK_SIZE}",
            bytes.len()
        )));
    }
    Ok(bytes.to_vec())
}

/// Decode the bitmap map { u16 => u64 } with bounds checking.
fn decode_bitmap(d: &mut Decoder<'_>) -> Result<BTreeMap<u16, u64>, DecodeError> {
    let len = d.map()?;
    match len {
        Some(n) => {
            let n = n as usize;
            if n > MAX_BITMAP_ENTRIES {
                return Err(DecodeError::message(format!(
                    "bitmap has {n} entries, maximum is {MAX_BITMAP_ENTRIES}"
                )));
            }
            let mut bitmap = BTreeMap::new();
            for _ in 0..n {
                let index = d.u16()?;
                let bits = d.u64()?;
                bitmap.insert(index, bits);
            }
            Ok(bitmap)
        }
        None => {
            let mut bitmap = BTreeMap::new();
            loop {
                if d.datatype()? == minicbor::data::Type::Break {
                    d.skip()?;
                    break;
                }
                if bitmap.len() >= MAX_BITMAP_ENTRIES {
                    return Err(DecodeError::message(format!(
                        "bitmap exceeds maximum of {MAX_BITMAP_ENTRIES} entries"
                    )));
                }
                let index = d.u16()?;
                let bits = d.u64()?;
                bitmap.insert(index, bits);
            }
            Ok(bitmap)
        }
    }
}

/// Decode a list of opaque byte blobs with count and per-item size limits.
fn decode_blob_list(
    d: &mut Decoder<'_>,
    max_count: usize,
    max_item_size: usize,
    item_name: &str,
) -> Result<Vec<Vec<u8>>, DecodeError> {
    let len = d.array()?;
    match len {
        Some(n) => {
            let n = n as usize;
            if n > max_count {
                return Err(DecodeError::message(format!(
                    "{item_name} list has {n} entries, maximum is {max_count}"
                )));
            }
            let mut items = Vec::with_capacity(n);
            for _ in 0..n {
                items.push(decode_bounded_bytes(d, max_item_size, item_name)?);
            }
            Ok(items)
        }
        None => {
            let mut items = Vec::new();
            loop {
                if d.datatype()? == minicbor::data::Type::Break {
                    d.skip()?;
                    break;
                }
                if items.len() >= max_count {
                    return Err(DecodeError::message(format!(
                        "{item_name} list exceeds maximum of {max_count}"
                    )));
                }
                items.push(decode_bounded_bytes(d, max_item_size, item_name)?);
            }
            Ok(items)
        }
    }
}

/// Decode bytes with a size limit.
fn decode_bounded_bytes(
    d: &mut Decoder<'_>,
    max_size: usize,
    name: &str,
) -> Result<Vec<u8>, DecodeError> {
    let bytes = d.bytes()?;
    if bytes.len() > max_size {
        return Err(DecodeError::message(format!(
            "{name} is {} bytes, maximum is {max_size}",
            bytes.len()
        )));
    }
    Ok(bytes.to_vec())
}

/// Decode a list of (slot, voter_id) pairs with bounds checking.
fn decode_vote_id_list(d: &mut Decoder<'_>) -> Result<Vec<(u64, Vec<u8>)>, DecodeError> {
    let len = d.array()?;
    match len {
        Some(n) => {
            let n = n as usize;
            if n > MAX_VOTES {
                return Err(DecodeError::message(format!(
                    "vote ID list has {n} entries, maximum is {MAX_VOTES}"
                )));
            }
            let mut votes = Vec::with_capacity(n);
            for _ in 0..n {
                votes.push(decode_vote_id_pair(d)?);
            }
            Ok(votes)
        }
        None => {
            let mut votes = Vec::new();
            loop {
                if d.datatype()? == minicbor::data::Type::Break {
                    d.skip()?;
                    break;
                }
                if votes.len() >= MAX_VOTES {
                    return Err(DecodeError::message(format!(
                        "vote ID list exceeds maximum of {MAX_VOTES}"
                    )));
                }
                votes.push(decode_vote_id_pair(d)?);
            }
            Ok(votes)
        }
    }
}

/// Decode a single (slot, voter_id) pair.
fn decode_vote_id_pair(d: &mut Decoder<'_>) -> Result<(u64, Vec<u8>), DecodeError> {
    let _pair_len = d.array()?;
    let slot = d.u64()?;
    let voter_id = d.bytes()?;
    if voter_id.len() > MAX_VOTER_ID_SIZE {
        return Err(DecodeError::message(format!(
            "voter ID is {} bytes, maximum is {MAX_VOTER_ID_SIZE}",
            voter_id.len()
        )));
    }
    Ok((slot, voter_id.to_vec()))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn round_trip(msg: &Message) -> Message {
        let encoded = minicbor::to_vec(msg).unwrap();
        minicbor::decode(&encoded).unwrap()
    }

    fn test_hash() -> [u8; 32] {
        let mut h = [0u8; 32];
        h[0] = 0xAB;
        h[31] = 0xCD;
        h
    }

    // --- Round-trip tests ---

    #[test]
    fn block_request_round_trip() {
        let msg = Message::MsgLeiosBlockRequest {
            slot: 42,
            hash: test_hash(),
        };
        let decoded = round_trip(&msg);
        match decoded {
            Message::MsgLeiosBlockRequest { slot, hash } => {
                assert_eq!(slot, 42);
                assert_eq!(hash, test_hash());
            }
            other => panic!("expected MsgLeiosBlockRequest, got {other:?}"),
        }
    }

    #[test]
    fn block_round_trip() {
        let msg = Message::MsgLeiosBlock {
            block: vec![0xEB, 0x01, 0x02],
        };
        let decoded = round_trip(&msg);
        match decoded {
            Message::MsgLeiosBlock { block } => assert_eq!(block, vec![0xEB, 0x01, 0x02]),
            other => panic!("expected MsgLeiosBlock, got {other:?}"),
        }
    }

    #[test]
    fn block_txs_request_round_trip() {
        let mut bitmap = BTreeMap::new();
        bitmap.insert(0u16, 0xFFu64);
        bitmap.insert(5u16, 0x8000_0000_0000_0001u64);

        let msg = Message::MsgLeiosBlockTxsRequest {
            slot: 100,
            hash: test_hash(),
            bitmap,
        };
        let decoded = round_trip(&msg);
        match decoded {
            Message::MsgLeiosBlockTxsRequest { slot, hash, bitmap } => {
                assert_eq!(slot, 100);
                assert_eq!(hash, test_hash());
                assert_eq!(bitmap.len(), 2);
                assert_eq!(bitmap[&0], 0xFF);
                assert_eq!(bitmap[&5], 0x8000_0000_0000_0001);
            }
            other => panic!("expected MsgLeiosBlockTxsRequest, got {other:?}"),
        }
    }

    #[test]
    fn block_txs_request_empty_bitmap_round_trip() {
        let msg = Message::MsgLeiosBlockTxsRequest {
            slot: 0,
            hash: [0; 32],
            bitmap: BTreeMap::new(),
        };
        let decoded = round_trip(&msg);
        match decoded {
            Message::MsgLeiosBlockTxsRequest { bitmap, .. } => {
                assert!(bitmap.is_empty());
            }
            other => panic!("expected MsgLeiosBlockTxsRequest, got {other:?}"),
        }
    }

    #[test]
    fn block_txs_round_trip() {
        let msg = Message::MsgLeiosBlockTxs {
            transactions: vec![vec![0x01, 0x02], vec![0x03]],
        };
        let decoded = round_trip(&msg);
        match decoded {
            Message::MsgLeiosBlockTxs { transactions } => {
                assert_eq!(transactions.len(), 2);
                assert_eq!(transactions[0], vec![0x01, 0x02]);
                assert_eq!(transactions[1], vec![0x03]);
            }
            other => panic!("expected MsgLeiosBlockTxs, got {other:?}"),
        }
    }

    #[test]
    fn block_txs_empty_round_trip() {
        let msg = Message::MsgLeiosBlockTxs {
            transactions: vec![],
        };
        let decoded = round_trip(&msg);
        match decoded {
            Message::MsgLeiosBlockTxs { transactions } => assert!(transactions.is_empty()),
            other => panic!("expected MsgLeiosBlockTxs, got {other:?}"),
        }
    }

    #[test]
    fn votes_request_round_trip() {
        let msg = Message::MsgLeiosVotesRequest {
            votes: vec![(10, vec![0xAA]), (20, vec![0xBB, 0xCC])],
        };
        let decoded = round_trip(&msg);
        match decoded {
            Message::MsgLeiosVotesRequest { votes } => {
                assert_eq!(votes.len(), 2);
                assert_eq!(votes[0], (10, vec![0xAA]));
                assert_eq!(votes[1], (20, vec![0xBB, 0xCC]));
            }
            other => panic!("expected MsgLeiosVotesRequest, got {other:?}"),
        }
    }

    #[test]
    fn vote_delivery_round_trip() {
        let msg = Message::MsgLeiosVoteDelivery {
            votes: vec![vec![0x01, 0x02], vec![0x03, 0x04]],
        };
        let decoded = round_trip(&msg);
        match decoded {
            Message::MsgLeiosVoteDelivery { votes } => {
                assert_eq!(votes.len(), 2);
                assert_eq!(votes[0], vec![0x01, 0x02]);
            }
            other => panic!("expected MsgLeiosVoteDelivery, got {other:?}"),
        }
    }

    #[test]
    fn block_range_request_round_trip() {
        let msg = Message::MsgLeiosBlockRangeRequest {
            start_slot: 100,
            end_slot: 200,
            start_hash: test_hash(),
            end_hash: [0xFF; 32],
        };
        let decoded = round_trip(&msg);
        match decoded {
            Message::MsgLeiosBlockRangeRequest {
                start_slot,
                end_slot,
                start_hash,
                end_hash,
            } => {
                assert_eq!(start_slot, 100);
                assert_eq!(end_slot, 200);
                assert_eq!(start_hash, test_hash());
                assert_eq!(end_hash, [0xFF; 32]);
            }
            other => panic!("expected MsgLeiosBlockRangeRequest, got {other:?}"),
        }
    }

    #[test]
    fn next_block_in_range_round_trip() {
        let msg = Message::MsgLeiosNextBlockAndTxsInRange {
            block: vec![0xE1],
            transactions: vec![vec![0x01]],
        };
        let decoded = round_trip(&msg);
        match decoded {
            Message::MsgLeiosNextBlockAndTxsInRange {
                block,
                transactions,
            } => {
                assert_eq!(block, vec![0xE1]);
                assert_eq!(transactions, vec![vec![0x01]]);
            }
            other => panic!("expected MsgLeiosNextBlockAndTxsInRange, got {other:?}"),
        }
    }

    #[test]
    fn last_block_in_range_round_trip() {
        let msg = Message::MsgLeiosLastBlockAndTxsInRange {
            block: vec![0xE2],
            transactions: vec![vec![0x02], vec![0x03]],
        };
        let decoded = round_trip(&msg);
        match decoded {
            Message::MsgLeiosLastBlockAndTxsInRange {
                block,
                transactions,
            } => {
                assert_eq!(block, vec![0xE2]);
                assert_eq!(transactions.len(), 2);
            }
            other => panic!("expected MsgLeiosLastBlockAndTxsInRange, got {other:?}"),
        }
    }

    #[test]
    fn done_round_trip() {
        let decoded = round_trip(&Message::MsgDone);
        assert!(matches!(decoded, Message::MsgDone));
    }

    // --- Error cases ---

    #[test]
    fn unknown_tag_fails() {
        let bad = &[0x81, 0x18, 0x63]; // [99]
        let result: Result<Message, _> = minicbor::decode(bad);
        assert!(result.is_err());
    }

    #[test]
    fn decode_indefinite_outer_array() {
        // MsgDone [9] as indefinite: 0x9f 0x09 0xff
        let cbor = &[0x9f, 0x09, 0xff];
        let decoded: Message = minicbor::decode(cbor).unwrap();
        assert!(matches!(decoded, Message::MsgDone));
    }

    #[test]
    fn wrong_hash_length_fails() {
        let mut buf = Vec::new();
        let mut e = minicbor::Encoder::new(&mut buf);
        e.array(3).unwrap();
        e.u32(0).unwrap();
        e.u64(0).unwrap();
        e.bytes(&[0u8; 16]).unwrap(); // 16 bytes, not 32

        let result: Result<Message, _> = minicbor::decode(&buf);
        assert!(result.is_err());
    }

    #[test]
    fn bitmap_exceeds_max_fails() {
        let mut buf = Vec::new();
        let mut e = minicbor::Encoder::new(&mut buf);
        e.array(4).unwrap();
        e.u32(2).unwrap();
        e.u64(0).unwrap();
        e.bytes(&[0u8; 32]).unwrap();
        let n = MAX_BITMAP_ENTRIES + 1;
        e.map(n as u64).unwrap();
        for i in 0..n {
            e.u16(i as u16).unwrap();
            e.u64(1).unwrap();
        }

        let result: Result<Message, _> = minicbor::decode(&buf);
        assert!(result.is_err());
    }

    #[test]
    fn transaction_list_exceeds_max_fails() {
        let mut buf = Vec::new();
        let mut e = minicbor::Encoder::new(&mut buf);
        e.array(2).unwrap();
        e.u32(3).unwrap();
        let n = MAX_TRANSACTIONS + 1;
        e.array(n as u64).unwrap();
        for _ in 0..n {
            e.bytes(&[0x01]).unwrap();
        }

        let result: Result<Message, _> = minicbor::decode(&buf);
        assert!(result.is_err());
    }

    #[test]
    fn vote_delivery_exceeds_max_fails() {
        let mut buf = Vec::new();
        let mut e = minicbor::Encoder::new(&mut buf);
        e.array(2).unwrap();
        e.u32(5).unwrap();
        let n = MAX_VOTES + 1;
        e.array(n as u64).unwrap();
        for _ in 0..n {
            e.bytes(&[0x01]).unwrap();
        }

        let result: Result<Message, _> = minicbor::decode(&buf);
        assert!(result.is_err());
    }

    #[test]
    fn vote_request_exceeds_max_fails() {
        let mut buf = Vec::new();
        let mut e = minicbor::Encoder::new(&mut buf);
        e.array(2).unwrap();
        e.u32(4).unwrap();
        let n = MAX_VOTES + 1;
        e.array(n as u64).unwrap();
        for i in 0..n {
            e.array(2).unwrap();
            e.u64(i as u64).unwrap();
            e.bytes(&[0x01]).unwrap();
        }

        let result: Result<Message, _> = minicbor::decode(&buf);
        assert!(result.is_err());
    }

    #[test]
    fn truncated_message_fails() {
        let msg = Message::MsgLeiosBlockRequest {
            slot: 1,
            hash: test_hash(),
        };
        let encoded = minicbor::to_vec(&msg).unwrap();
        let truncated = &encoded[..3];
        let result: Result<Message, _> = minicbor::decode(truncated);
        assert!(result.is_err());
    }
}
