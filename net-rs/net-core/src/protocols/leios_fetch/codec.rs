//! CBOR encoding for LeiosFetch messages (CIP-0164 prototype,
//! cardano-blueprint `leios-prototype`).
//!
//! Wire format:
//!   msgLeiosBlockRequest    = [0, point]              point = [slot, hash32]
//!   msgLeiosBlock           = [1, endorser_block]     endorser_block = { hash => word32 }
//!   msgLeiosBlockTxsRequest = [2, point, bitmaps]     bitmaps = { word16 => word64 }
//!   msgLeiosBlockTxs        = [3, point, bitmaps, tx_list]   tx_list = [ *tx ]
//!   msgClientDone           = [9]
//!
//! `endorser_block` and each `tx` are carried as raw CBOR (opaque
//! pass-through): the codec splices/captures their bytes verbatim, so
//! the exact map/tx shape lives with the consumer, not here.

use std::collections::BTreeMap;

use minicbor::decode::Error as DecodeError;
use minicbor::encode::Error as EncodeError;
use minicbor::{Decoder, Encoder};

use super::{Message, MAX_BITMAP_ENTRIES, MAX_BLOCK_SIZE, MAX_TRANSACTIONS, MAX_TRANSACTION_SIZE};
use crate::types::Point;

impl minicbor::Encode<()> for Message {
    fn encode<W: minicbor::encode::Write>(
        &self,
        e: &mut Encoder<W>,
        _ctx: &mut (),
    ) -> Result<(), EncodeError<W::Error>> {
        match self {
            Message::MsgLeiosBlockRequest { point } => {
                e.array(2)?;
                e.u32(0)?;
                minicbor::Encode::encode(point, e, &mut ())?;
            }
            Message::MsgLeiosBlock { block } => {
                e.array(2)?;
                e.u32(1)?;
                // `block` is the raw CBOR `endorser_block` map — splice verbatim.
                encode_raw(e, block)?;
            }
            Message::MsgLeiosBlockTxsRequest { point, bitmap } => {
                e.array(3)?;
                e.u32(2)?;
                minicbor::Encode::encode(point, e, &mut ())?;
                encode_bitmap(e, bitmap)?;
            }
            Message::MsgLeiosBlockTxs {
                point,
                bitmap,
                transactions,
            } => {
                e.array(4)?;
                e.u32(3)?;
                minicbor::Encode::encode(point, e, &mut ())?;
                encode_bitmap(e, bitmap)?;
                encode_tx_list(e, transactions)?;
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
                let point = Point::decode(d, &mut ())?;
                Ok(Message::MsgLeiosBlockRequest { point })
            }
            1 => {
                // endorser_block is a CBOR map { tx_hash => tx_size };
                // captured as raw bytes for opaque pass-through.
                let block = decode_raw_bounded(d, MAX_BLOCK_SIZE, "endorser block")?;
                Ok(Message::MsgLeiosBlock { block })
            }
            2 => {
                let point = Point::decode(d, &mut ())?;
                let bitmap = decode_bitmap(d)?;
                Ok(Message::MsgLeiosBlockTxsRequest { point, bitmap })
            }
            3 => {
                let point = Point::decode(d, &mut ())?;
                let bitmap = decode_bitmap(d)?;
                let transactions = decode_tx_list(d)?;
                Ok(Message::MsgLeiosBlockTxs {
                    point,
                    bitmap,
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
    // Indefinite-length map per the leios-prototype CDDL:
    //   bitmaps = { * base.word16 => base.word64 }  ; indefinite-length
    // The prototype relay's parser rejects the definite-length form
    // and immediately RSTs the bearer on receipt.
    e.begin_map()?;
    for (index, bits) in bitmap {
        e.u16(*index)?;
        e.u64(*bits)?;
    }
    e.end()?;
    Ok(())
}

/// Encode a tx list `[ tx, ... ]`, splicing each tx's raw CBOR verbatim
/// (txs are opaque pass-through — `tx.tx` may be any CBOR shape).
fn encode_tx_list<W: minicbor::encode::Write>(
    e: &mut Encoder<W>,
    txs: &[Vec<u8>],
) -> Result<(), EncodeError<W::Error>> {
    e.array(txs.len() as u64)?;
    for tx in txs {
        encode_raw(e, tx)?;
    }
    Ok(())
}

/// Splice a raw, already-CBOR-encoded value into the output verbatim.
fn encode_raw<W: minicbor::encode::Write>(
    e: &mut Encoder<W>,
    raw: &[u8],
) -> Result<(), EncodeError<W::Error>> {
    e.writer_mut().write_all(raw).map_err(EncodeError::write)
}

// --- Decode helpers ---

/// Capture the next CBOR value's raw bytes verbatim (opaque pass-through),
/// enforcing a size bound.
fn decode_raw_bounded(
    d: &mut Decoder<'_>,
    max_size: usize,
    name: &str,
) -> Result<Vec<u8>, DecodeError> {
    let start = d.position();
    d.skip()?;
    let raw = &d.input()[start..d.position()];
    if raw.len() > max_size {
        return Err(DecodeError::message(format!(
            "{name} is {} bytes, maximum is {max_size}",
            raw.len()
        )));
    }
    Ok(raw.to_vec())
}

/// Decode a tx list, capturing each tx's raw CBOR (count- and
/// size-bounded).
fn decode_tx_list(d: &mut Decoder<'_>) -> Result<Vec<Vec<u8>>, DecodeError> {
    let len = d.array()?;
    match len {
        Some(n) => {
            let n = n as usize;
            if n > MAX_TRANSACTIONS {
                return Err(DecodeError::message(format!(
                    "transaction list has {n} entries, maximum is {MAX_TRANSACTIONS}"
                )));
            }
            let mut items = Vec::with_capacity(n);
            for _ in 0..n {
                items.push(decode_raw_bounded(d, MAX_TRANSACTION_SIZE, "transaction")?);
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
                if items.len() >= MAX_TRANSACTIONS {
                    return Err(DecodeError::message(format!(
                        "transaction list exceeds maximum of {MAX_TRANSACTIONS}"
                    )));
                }
                items.push(decode_raw_bounded(d, MAX_TRANSACTION_SIZE, "transaction")?);
            }
            Ok(items)
        }
    }
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::types::Point;

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
            point: Point::Specific {
                slot: 42,
                hash: test_hash(),
            },
        };
        let decoded = round_trip(&msg);
        match decoded {
            Message::MsgLeiosBlockRequest { point } => {
                assert_eq!(
                    point,
                    Point::Specific {
                        slot: 42,
                        hash: test_hash(),
                    }
                );
            }
            other => panic!("expected MsgLeiosBlockRequest, got {other:?}"),
        }
    }

    #[test]
    fn block_round_trip() {
        // `block` is raw CBOR — a `{ hash => size }` manifest map.  Built
        // here as a 1-entry map: 0xA1 (map(1)) + 0x5820<32B hash> + 0x18 0x2A (42).
        let mut block = vec![0xA1, 0x58, 0x20];
        block.extend_from_slice(&test_hash());
        block.extend_from_slice(&[0x18, 0x2A]);
        let msg = Message::MsgLeiosBlock {
            block: block.clone(),
        };
        let decoded = round_trip(&msg);
        match decoded {
            // The raw manifest bytes round-trip verbatim.
            Message::MsgLeiosBlock { block: got } => assert_eq!(got, block),
            other => panic!("expected MsgLeiosBlock, got {other:?}"),
        }
    }

    #[test]
    fn block_txs_request_round_trip() {
        let mut bitmap = BTreeMap::new();
        bitmap.insert(0u16, 0xFFu64);
        bitmap.insert(5u16, 0x8000_0000_0000_0001u64);

        let msg = Message::MsgLeiosBlockTxsRequest {
            point: Point::Specific {
                slot: 100,
                hash: test_hash(),
            },
            bitmap,
        };
        let decoded = round_trip(&msg);
        match decoded {
            Message::MsgLeiosBlockTxsRequest { point, bitmap } => {
                assert_eq!(
                    point,
                    Point::Specific {
                        slot: 100,
                        hash: test_hash(),
                    }
                );
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
            point: Point::Specific {
                slot: 0,
                hash: [0; 32],
            },
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

    /// A single CBOR value used as an opaque tx in tests (uint).
    fn tx(n: u8) -> Vec<u8> {
        vec![n] // 0..=23 encode as a 1-byte CBOR uint
    }

    #[test]
    fn block_txs_round_trip() {
        let mut bitmap = BTreeMap::new();
        bitmap.insert(0u16, 0x3u64);
        let msg = Message::MsgLeiosBlockTxs {
            point: Point::Specific {
                slot: 7,
                hash: test_hash(),
            },
            bitmap,
            transactions: vec![tx(1), tx(2)],
        };
        let decoded = round_trip(&msg);
        match decoded {
            Message::MsgLeiosBlockTxs {
                point,
                bitmap,
                transactions,
            } => {
                assert_eq!(
                    point,
                    Point::Specific {
                        slot: 7,
                        hash: test_hash()
                    }
                );
                assert_eq!(bitmap[&0], 0x3);
                assert_eq!(transactions, vec![tx(1), tx(2)]);
            }
            other => panic!("expected MsgLeiosBlockTxs, got {other:?}"),
        }
    }

    #[test]
    fn block_txs_empty_round_trip() {
        let msg = Message::MsgLeiosBlockTxs {
            point: Point::Specific {
                slot: 0,
                hash: [0; 32],
            },
            bitmap: BTreeMap::new(),
            transactions: vec![],
        };
        let decoded = round_trip(&msg);
        match decoded {
            Message::MsgLeiosBlockTxs { transactions, .. } => assert!(transactions.is_empty()),
            other => panic!("expected MsgLeiosBlockTxs, got {other:?}"),
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
        // MsgLeiosBlockRequest [0, [0, bytes(16)]] — point with hash too short
        let mut buf = Vec::new();
        let mut e = minicbor::Encoder::new(&mut buf);
        e.array(2).unwrap();
        e.u32(0).unwrap();
        e.array(2).unwrap();
        e.u64(0).unwrap();
        e.bytes(&[0u8; 16]).unwrap(); // 16 bytes, not 32

        let result: Result<Message, _> = minicbor::decode(&buf);
        assert!(result.is_err());
    }

    #[test]
    fn bitmap_exceeds_max_fails() {
        let mut buf = Vec::new();
        let mut e = minicbor::Encoder::new(&mut buf);
        e.array(3).unwrap();
        e.u32(2).unwrap();
        // encode point sub-array
        e.array(2).unwrap();
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
        e.array(4).unwrap();
        e.u32(3).unwrap();
        // point
        e.array(2).unwrap();
        e.u64(0).unwrap();
        e.bytes(&[0u8; 32]).unwrap();
        // empty bitmap
        e.map(0).unwrap();
        // oversized tx list
        let n = MAX_TRANSACTIONS + 1;
        e.array(n as u64).unwrap();
        for _ in 0..n {
            e.u8(1).unwrap();
        }

        let result: Result<Message, _> = minicbor::decode(&buf);
        assert!(result.is_err());
    }

    #[test]
    fn truncated_message_fails() {
        let msg = Message::MsgLeiosBlockRequest {
            point: Point::Specific {
                slot: 1,
                hash: test_hash(),
            },
        };
        let encoded = minicbor::to_vec(&msg).unwrap();
        let truncated = &encoded[..3];
        let result: Result<Message, _> = minicbor::decode(truncated);
        assert!(result.is_err());
    }
}
