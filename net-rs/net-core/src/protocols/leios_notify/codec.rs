//! CBOR encoding for LeiosNotify messages.
//!
//! Wire format:
//!   msgLeiosNotificationRequestNext = [0]
//!   msgLeiosBlockAnnouncement       = [1, wrappedHeader]
//!   msgLeiosBlockOffer              = [2, point]        where point = [slot, hash32]
//!   msgLeiosBlockTxsOffer           = [3, point]        where point = [slot, hash32]
//!   msgLeiosVotesOffer              = [4, [(slot, voterId), ...]]
//!   msgDone                         = [5]

use minicbor::decode::Error as DecodeError;
use minicbor::encode::Error as EncodeError;
use minicbor::{Decoder, Encoder};

use super::{Message, MAX_VOTER_ID_SIZE, MAX_VOTES_OFFERED};
use crate::types::{Point, WrappedHeader};

impl minicbor::Encode<()> for Message {
    fn encode<W: minicbor::encode::Write>(
        &self,
        e: &mut Encoder<W>,
        _ctx: &mut (),
    ) -> Result<(), EncodeError<W::Error>> {
        match self {
            Message::MsgLeiosNotificationRequestNext => {
                e.array(1)?;
                e.u32(0)?;
            }
            Message::MsgLeiosBlockAnnouncement { header } => {
                e.array(2)?;
                e.u32(1)?;
                minicbor::Encode::encode(header, e, &mut ())?;
            }
            Message::MsgLeiosBlockOffer { point } => {
                e.array(2)?;
                e.u32(2)?;
                minicbor::Encode::encode(point, e, &mut ())?;
            }
            Message::MsgLeiosBlockTxsOffer { point } => {
                e.array(2)?;
                e.u32(3)?;
                minicbor::Encode::encode(point, e, &mut ())?;
            }
            Message::MsgLeiosVotesOffer { votes } => {
                e.array(2)?;
                e.u32(4)?;
                e.array(votes.len() as u64)?;
                for (slot, voter_id) in votes {
                    e.array(2)?;
                    e.u64(*slot)?;
                    e.bytes(voter_id)?;
                }
            }
            Message::MsgDone => {
                e.array(1)?;
                e.u32(5)?;
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
            0 => Ok(Message::MsgLeiosNotificationRequestNext),
            1 => {
                let header = WrappedHeader::decode(d, &mut ())?;
                Ok(Message::MsgLeiosBlockAnnouncement { header })
            }
            2 => {
                let point = Point::decode(d, &mut ())?;
                Ok(Message::MsgLeiosBlockOffer { point })
            }
            3 => {
                let point = Point::decode(d, &mut ())?;
                Ok(Message::MsgLeiosBlockTxsOffer { point })
            }
            4 => {
                let votes = decode_vote_offers(d)?;
                Ok(Message::MsgLeiosVotesOffer { votes })
            }
            5 => Ok(Message::MsgDone),
            other => Err(DecodeError::message(format!(
                "unknown leios_notify message tag: {other}"
            ))),
        }
    }
}

/// Decode a list of (slot, voter_id) pairs with bounds checking.
fn decode_vote_offers(d: &mut Decoder<'_>) -> Result<Vec<(u64, Vec<u8>)>, DecodeError> {
    let len = d.array()?;
    match len {
        Some(n) => {
            let n = n as usize;
            if n > MAX_VOTES_OFFERED {
                return Err(DecodeError::message(format!(
                    "votes offer list has {n} entries, maximum is {MAX_VOTES_OFFERED}"
                )));
            }
            let mut votes = Vec::with_capacity(n);
            for _ in 0..n {
                votes.push(decode_vote_offer_pair(d)?);
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
                if votes.len() >= MAX_VOTES_OFFERED {
                    return Err(DecodeError::message(format!(
                        "votes offer list exceeds maximum of {MAX_VOTES_OFFERED}"
                    )));
                }
                votes.push(decode_vote_offer_pair(d)?);
            }
            Ok(votes)
        }
    }
}

/// Decode a single (slot, voter_id) pair.
fn decode_vote_offer_pair(d: &mut Decoder<'_>) -> Result<(u64, Vec<u8>), DecodeError> {
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

    #[test]
    fn request_next_round_trip() {
        let decoded = round_trip(&Message::MsgLeiosNotificationRequestNext);
        assert!(matches!(decoded, Message::MsgLeiosNotificationRequestNext));
    }

    #[test]
    fn block_announcement_round_trip() {
        let msg = Message::MsgLeiosBlockAnnouncement {
            header: WrappedHeader::opaque(vec![0x82, 0x05, 0x00]),
        };
        let decoded = round_trip(&msg);
        match decoded {
            Message::MsgLeiosBlockAnnouncement { header } => {
                assert_eq!(header.raw, vec![0x82, 0x05, 0x00]);
            }
            other => panic!("expected MsgLeiosBlockAnnouncement, got {other:?}"),
        }
    }

    #[test]
    fn block_offer_round_trip() {
        let msg = Message::MsgLeiosBlockOffer {
            point: Point::Specific {
                slot: 42,
                hash: test_hash(),
            },
        };
        let decoded = round_trip(&msg);
        match decoded {
            Message::MsgLeiosBlockOffer { point } => {
                assert_eq!(
                    point,
                    Point::Specific {
                        slot: 42,
                        hash: test_hash(),
                    }
                );
            }
            other => panic!("expected MsgLeiosBlockOffer, got {other:?}"),
        }
    }

    #[test]
    fn block_txs_offer_round_trip() {
        let msg = Message::MsgLeiosBlockTxsOffer {
            point: Point::Specific {
                slot: 99,
                hash: test_hash(),
            },
        };
        let decoded = round_trip(&msg);
        match decoded {
            Message::MsgLeiosBlockTxsOffer { point } => {
                assert_eq!(
                    point,
                    Point::Specific {
                        slot: 99,
                        hash: test_hash(),
                    }
                );
            }
            other => panic!("expected MsgLeiosBlockTxsOffer, got {other:?}"),
        }
    }

    #[test]
    fn votes_offer_round_trip() {
        let msg = Message::MsgLeiosVotesOffer {
            votes: vec![(100, vec![0x01, 0x02, 0x03]), (200, vec![0x04, 0x05])],
        };
        let decoded = round_trip(&msg);
        match decoded {
            Message::MsgLeiosVotesOffer { votes } => {
                assert_eq!(votes.len(), 2);
                assert_eq!(votes[0], (100, vec![0x01, 0x02, 0x03]));
                assert_eq!(votes[1], (200, vec![0x04, 0x05]));
            }
            other => panic!("expected MsgLeiosVotesOffer, got {other:?}"),
        }
    }

    #[test]
    fn votes_offer_empty_round_trip() {
        let msg = Message::MsgLeiosVotesOffer { votes: vec![] };
        let decoded = round_trip(&msg);
        match decoded {
            Message::MsgLeiosVotesOffer { votes } => assert!(votes.is_empty()),
            other => panic!("expected MsgLeiosVotesOffer, got {other:?}"),
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
    fn decode_indefinite_outer_array() {
        // MsgDone [5] as indefinite: 0x9f 0x05 0xff
        let cbor = &[0x9f, 0x05, 0xff];
        let decoded: Message = minicbor::decode(cbor).unwrap();
        assert!(matches!(decoded, Message::MsgDone));
    }

    #[test]
    fn wrong_hash_length_fails() {
        // MsgLeiosBlockOffer [2, [0, bytes(16)]] — point with hash too short
        let mut buf = Vec::new();
        let mut e = minicbor::Encoder::new(&mut buf);
        e.array(2).unwrap();
        e.u32(2).unwrap();
        e.array(2).unwrap();
        e.u64(0).unwrap();
        e.bytes(&[0u8; 16]).unwrap(); // 16 bytes, not 32

        let result: Result<Message, _> = minicbor::decode(&buf);
        assert!(result.is_err());
    }

    #[test]
    fn votes_offer_exceeds_max_fails() {
        // Build a MsgLeiosVotesOffer with MAX_VOTES_OFFERED + 1 entries.
        let mut buf = Vec::new();
        let mut e = minicbor::Encoder::new(&mut buf);
        e.array(2).unwrap();
        e.u32(4).unwrap();
        let n = MAX_VOTES_OFFERED + 1;
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
    fn truncated_block_offer_fails() {
        let msg = Message::MsgLeiosBlockOffer {
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
