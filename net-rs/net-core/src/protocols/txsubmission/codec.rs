//! CBOR encoding for TxSubmission messages.
//!
//! Wire format (from spec section 3.8):
//!
//!   msgInit          = [6]
//!   msgRequestTxIds  = [0, tsBlocking, txCount, txCount]
//!   msgReplyTxIds    = [1, txIdsAndSizes]
//!   msgRequestTxs    = [2, txIdList]
//!   msgReplyTxs      = [3, txList]
//!   tsMsgDone        = [4]
//!
//! Inner lists (txIdsAndSizes, txIdList, txList) use indefinite-length
//! encoding per the Haskell codec.

use minicbor::decode::Error as DecodeError;
use minicbor::encode::Error as EncodeError;
use minicbor::{Decoder, Encoder};

use super::{Message, TxBody, TxId, TxIdAndSize, MAX_TX_ID_SIZE, MAX_TX_SIZE, MAX_UNACKED};

// --- TxId encode/decode ---
//
// `TxId(_)` carries the raw transaction-id bytes (e.g. the blake2b-256 hash).
// The codec wraps them as CBOR `bytes(N)` on the wire so the receiver can
// recover the same bytes on decode.

impl minicbor::Encode<()> for TxId {
    fn encode<W: minicbor::encode::Write>(
        &self,
        e: &mut Encoder<W>,
        _ctx: &mut (),
    ) -> Result<(), EncodeError<W::Error>> {
        e.bytes(&self.0)?;
        Ok(())
    }
}

impl<'a> minicbor::Decode<'a, ()> for TxId {
    fn decode(d: &mut Decoder<'a>, _ctx: &mut ()) -> Result<Self, DecodeError> {
        let raw = d.bytes()?;
        if raw.len() > MAX_TX_ID_SIZE {
            return Err(DecodeError::message(format!(
                "tx id too large: {} bytes exceeds limit {MAX_TX_ID_SIZE}",
                raw.len()
            )));
        }
        Ok(TxId(raw.to_vec()))
    }
}

// --- TxBody encode/decode ---
//
// `TxBody(_)` carries the raw transaction bytes; same wrapping pattern as
// `TxId`.

impl minicbor::Encode<()> for TxBody {
    fn encode<W: minicbor::encode::Write>(
        &self,
        e: &mut Encoder<W>,
        _ctx: &mut (),
    ) -> Result<(), EncodeError<W::Error>> {
        e.bytes(&self.0)?;
        Ok(())
    }
}

impl<'a> minicbor::Decode<'a, ()> for TxBody {
    fn decode(d: &mut Decoder<'a>, _ctx: &mut ()) -> Result<Self, DecodeError> {
        let raw = d.bytes()?;
        if raw.len() > MAX_TX_SIZE {
            return Err(DecodeError::message(format!(
                "tx body too large: {} bytes exceeds limit {MAX_TX_SIZE}",
                raw.len()
            )));
        }
        Ok(TxBody(raw.to_vec()))
    }
}

// --- TxIdAndSize encode/decode ---

impl minicbor::Encode<()> for TxIdAndSize {
    fn encode<W: minicbor::encode::Write>(
        &self,
        e: &mut Encoder<W>,
        _ctx: &mut (),
    ) -> Result<(), EncodeError<W::Error>> {
        e.array(2)?;
        self.tx_id.encode(e, &mut ())?;
        e.u32(self.size)?;
        Ok(())
    }
}

impl<'a> minicbor::Decode<'a, ()> for TxIdAndSize {
    fn decode(d: &mut Decoder<'a>, _ctx: &mut ()) -> Result<Self, DecodeError> {
        let _len = d.array()?;
        let tx_id = TxId::decode(d, &mut ())?;
        let size = d.u32()?;
        Ok(TxIdAndSize { tx_id, size })
    }
}

// --- Helpers for indefinite-length list encode/decode ---

/// Decode an indefinite-or-definite-length list with a bound.
fn decode_bounded_list<'a, T, F>(
    d: &mut Decoder<'a>,
    max: usize,
    name: &str,
    mut decode_item: F,
) -> Result<Vec<T>, DecodeError>
where
    F: FnMut(&mut Decoder<'a>) -> Result<T, DecodeError>,
{
    let len = d.array()?;
    match len {
        Some(n) => {
            let n = n as usize;
            if n > max {
                return Err(DecodeError::message(format!(
                    "{name} list has {n} entries, maximum is {max}"
                )));
            }
            let mut items = Vec::with_capacity(n);
            for _ in 0..n {
                items.push(decode_item(d)?);
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
                if items.len() >= max {
                    return Err(DecodeError::message(format!(
                        "{name} list exceeds maximum of {max}"
                    )));
                }
                items.push(decode_item(d)?);
            }
            Ok(items)
        }
    }
}

// --- Message encode/decode ---

impl minicbor::Encode<()> for Message {
    fn encode<W: minicbor::encode::Write>(
        &self,
        e: &mut Encoder<W>,
        _ctx: &mut (),
    ) -> Result<(), EncodeError<W::Error>> {
        match self {
            Message::MsgInit => {
                e.array(1)?;
                e.u32(6)?;
            }
            Message::MsgRequestTxIdsBlocking { ack, req } => {
                e.array(4)?;
                e.u32(0)?;
                e.bool(true)?;
                e.u16(*ack)?;
                e.u16(*req)?;
            }
            Message::MsgRequestTxIdsNonBlocking { ack, req } => {
                e.array(4)?;
                e.u32(0)?;
                e.bool(false)?;
                e.u16(*ack)?;
                e.u16(*req)?;
            }
            Message::MsgReplyTxIds { tx_ids } => {
                e.array(2)?;
                e.u32(1)?;
                // Inner list: indefinite-length per Haskell codec.
                e.begin_array()?;
                for item in tx_ids {
                    item.encode(e, &mut ())?;
                }
                e.end()?;
            }
            Message::MsgRequestTxs { tx_ids } => {
                e.array(2)?;
                e.u32(2)?;
                // Inner list: indefinite-length.
                e.begin_array()?;
                for id in tx_ids {
                    id.encode(e, &mut ())?;
                }
                e.end()?;
            }
            Message::MsgReplyTxs { txs } => {
                e.array(2)?;
                e.u32(3)?;
                // Inner list: indefinite-length.
                e.begin_array()?;
                for tx in txs {
                    tx.encode(e, &mut ())?;
                }
                e.end()?;
            }
            Message::MsgDone => {
                e.array(1)?;
                e.u32(4)?;
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
            6 => Ok(Message::MsgInit),
            0 => {
                let blocking = d.bool()?;
                let ack = d.u16()?;
                let req = d.u16()?;
                if blocking {
                    Ok(Message::MsgRequestTxIdsBlocking { ack, req })
                } else {
                    Ok(Message::MsgRequestTxIdsNonBlocking { ack, req })
                }
            }
            1 => {
                let tx_ids = decode_bounded_list(d, MAX_UNACKED, "txIdsAndSizes", |d| {
                    TxIdAndSize::decode(d, &mut ())
                })?;
                Ok(Message::MsgReplyTxIds { tx_ids })
            }
            2 => {
                let tx_ids =
                    decode_bounded_list(d, MAX_UNACKED, "txIdList", |d| TxId::decode(d, &mut ()))?;
                Ok(Message::MsgRequestTxs { tx_ids })
            }
            3 => {
                let txs =
                    decode_bounded_list(d, MAX_UNACKED, "txList", |d| TxBody::decode(d, &mut ()))?;
                Ok(Message::MsgReplyTxs { txs })
            }
            4 => Ok(Message::MsgDone),
            other => Err(DecodeError::message(format!(
                "unknown txsubmission message tag: {other}"
            ))),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn round_trip(msg: &Message) -> Message {
        let encoded = minicbor::to_vec(msg).unwrap();
        minicbor::decode(&encoded).unwrap()
    }

    fn make_tx_id() -> TxId {
        TxId(vec![0xaa; 32])
    }

    fn make_tx_body(payload: &[u8]) -> TxBody {
        TxBody(payload.to_vec())
    }

    #[test]
    fn init_round_trip() {
        let decoded = round_trip(&Message::MsgInit);
        assert!(matches!(decoded, Message::MsgInit));
    }

    #[test]
    fn request_tx_ids_blocking_round_trip() {
        let msg = Message::MsgRequestTxIdsBlocking { ack: 3, req: 5 };
        let decoded = round_trip(&msg);
        match decoded {
            Message::MsgRequestTxIdsBlocking { ack, req } => {
                assert_eq!(ack, 3);
                assert_eq!(req, 5);
            }
            other => panic!("expected MsgRequestTxIdsBlocking, got {other:?}"),
        }
    }

    #[test]
    fn request_tx_ids_non_blocking_round_trip() {
        let msg = Message::MsgRequestTxIdsNonBlocking { ack: 0, req: 10 };
        let decoded = round_trip(&msg);
        match decoded {
            Message::MsgRequestTxIdsNonBlocking { ack, req } => {
                assert_eq!(ack, 0);
                assert_eq!(req, 10);
            }
            other => panic!("expected MsgRequestTxIdsNonBlocking, got {other:?}"),
        }
    }

    #[test]
    fn reply_tx_ids_round_trip() {
        let msg = Message::MsgReplyTxIds {
            tx_ids: vec![TxIdAndSize {
                tx_id: make_tx_id(),
                size: 1500,
            }],
        };
        let decoded = round_trip(&msg);
        match decoded {
            Message::MsgReplyTxIds { tx_ids } => {
                assert_eq!(tx_ids.len(), 1);
                assert_eq!(tx_ids[0].size, 1500);
            }
            other => panic!("expected MsgReplyTxIds, got {other:?}"),
        }
    }

    #[test]
    fn reply_tx_ids_empty_round_trip() {
        let msg = Message::MsgReplyTxIds { tx_ids: vec![] };
        let decoded = round_trip(&msg);
        match decoded {
            Message::MsgReplyTxIds { tx_ids } => assert!(tx_ids.is_empty()),
            other => panic!("expected MsgReplyTxIds, got {other:?}"),
        }
    }

    #[test]
    fn request_txs_round_trip() {
        let msg = Message::MsgRequestTxs {
            tx_ids: vec![make_tx_id(), make_tx_id()],
        };
        let decoded = round_trip(&msg);
        match decoded {
            Message::MsgRequestTxs { tx_ids } => assert_eq!(tx_ids.len(), 2),
            other => panic!("expected MsgRequestTxs, got {other:?}"),
        }
    }

    #[test]
    fn reply_txs_round_trip() {
        let msg = Message::MsgReplyTxs {
            txs: vec![make_tx_body(&[1, 2, 3]), make_tx_body(&[4, 5, 6])],
        };
        let decoded = round_trip(&msg);
        match decoded {
            Message::MsgReplyTxs { txs } => {
                assert_eq!(txs.len(), 2);
            }
            other => panic!("expected MsgReplyTxs, got {other:?}"),
        }
    }

    #[test]
    fn reply_txs_empty_round_trip() {
        let msg = Message::MsgReplyTxs { txs: vec![] };
        let decoded = round_trip(&msg);
        match decoded {
            Message::MsgReplyTxs { txs } => assert!(txs.is_empty()),
            other => panic!("expected MsgReplyTxs, got {other:?}"),
        }
    }

    #[test]
    fn done_round_trip() {
        let decoded = round_trip(&Message::MsgDone);
        assert!(matches!(decoded, Message::MsgDone));
    }

    #[test]
    fn unknown_tag_fails() {
        let bad = &[0x81, 0x18, 0x63]; // [99]
        let result: Result<Message, _> = minicbor::decode(bad);
        assert!(result.is_err());
    }

    #[test]
    fn truncated_request_fails() {
        let msg = Message::MsgRequestTxIdsBlocking { ack: 1, req: 2 };
        let encoded = minicbor::to_vec(&msg).unwrap();
        let truncated = &encoded[..3];
        let result: Result<Message, _> = minicbor::decode(truncated);
        assert!(result.is_err());
    }

    #[test]
    fn raw_hash_tx_id_round_trips_preserving_bytes() {
        // Production constructs `TxId(blake2b256(body))` with the raw 32-byte
        // hash, not pre-encoded CBOR. The codec must wrap on send and unwrap
        // on receive so the same bytes survive a round trip.
        let raw_hash: Vec<u8> = (0..32).collect();
        let msg = Message::MsgReplyTxIds {
            tx_ids: vec![TxIdAndSize {
                tx_id: TxId(raw_hash.clone()),
                size: 1234,
            }],
        };
        let decoded = round_trip(&msg);
        match decoded {
            Message::MsgReplyTxIds { tx_ids } => {
                assert_eq!(tx_ids.len(), 1);
                assert_eq!(tx_ids[0].tx_id.0, raw_hash);
                assert_eq!(tx_ids[0].size, 1234);
            }
            other => panic!("expected MsgReplyTxIds, got {other:?}"),
        }
    }

    #[test]
    fn raw_tx_body_round_trips_preserving_bytes() {
        // Bodies arrive from peers as raw transaction bytes; the codec
        // must CBOR-wrap them on the wire and recover the originals.
        let body_a: Vec<u8> = (0..200).map(|i| (i * 7) as u8).collect();
        let body_b: Vec<u8> = (0..1500).map(|i| (i * 31) as u8).collect();
        let msg = Message::MsgReplyTxs {
            txs: vec![TxBody(body_a.clone()), TxBody(body_b.clone())],
        };
        let decoded = round_trip(&msg);
        match decoded {
            Message::MsgReplyTxs { txs } => {
                assert_eq!(txs.len(), 2);
                assert_eq!(txs[0].0, body_a);
                assert_eq!(txs[1].0, body_b);
            }
            other => panic!("expected MsgReplyTxs, got {other:?}"),
        }
    }

    #[test]
    fn decode_indefinite_outer_array() {
        // MsgInit [6] as indefinite: 0x9f 0x06 0xff
        let cbor = &[0x9f, 0x06, 0xff];
        let decoded: Message = minicbor::decode(cbor).unwrap();
        assert!(matches!(decoded, Message::MsgInit));
    }

    #[test]
    fn decode_definite_inner_list() {
        // MsgReplyTxIds with definite-length inner list (should also work).
        let tx_id = make_tx_id();
        let mut buf = Vec::new();
        let mut e = minicbor::Encoder::new(&mut buf);
        e.array(2).unwrap();
        e.u32(1).unwrap();
        // Definite-length inner list with 1 element.
        e.array(1).unwrap();
        e.array(2).unwrap();
        minicbor::Encode::encode(&tx_id, &mut e, &mut ()).unwrap();
        e.u32(500).unwrap();

        let decoded: Message = minicbor::decode(&buf).unwrap();
        match decoded {
            Message::MsgReplyTxIds { tx_ids } => {
                assert_eq!(tx_ids.len(), 1);
                assert_eq!(tx_ids[0].size, 500);
            }
            other => panic!("expected MsgReplyTxIds, got {other:?}"),
        }
    }
}
