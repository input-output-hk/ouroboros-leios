//! CBOR encoding for LeiosNotify messages.
//!
//! Wire format (CIP-0164 prototype, cardano-blueprint `leios-prototype`):
//!   msgLeiosNotificationRequestNext = [0]
//!   msgLeiosBlockAnnouncement       = [1, announcement]
//!   msgLeiosBlockOffer              = [2, point, eb_size]   eb_size = word32
//!   msgLeiosBlockTxsOffer           = [3, point]            point = [slot, hash32]
//!   msgLeiosVotes                   = [4, [vote, ...]]
//!   msgClientDone                   = [5]
//!
//!   vote = [slot, eb_hash, voter_id, vote_signature]
//!     slot           : uint
//!     eb_hash        : bytes .size 32
//!     voter_id       : word16
//!     vote_signature : bool   (mocked; a real deployment carries a BLS sig)
//!
//! Decoders read the declared array length and skip any trailing
//! elements they don't recognise, so a future field addition degrades
//! gracefully instead of desyncing the mux stream.

use minicbor::decode::Error as DecodeError;
use minicbor::encode::Error as EncodeError;
use minicbor::{Decoder, Encoder};

use super::{Message, MAX_VOTES};
use crate::types::{Point, Vote, WrappedHeader};

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
            Message::MsgLeiosBlockOffer { point, eb_size } => {
                e.array(3)?;
                e.u32(2)?;
                minicbor::Encode::encode(point, e, &mut ())?;
                e.u32(*eb_size)?;
            }
            Message::MsgLeiosBlockTxsOffer { point } => {
                e.array(2)?;
                e.u32(3)?;
                minicbor::Encode::encode(point, e, &mut ())?;
            }
            Message::MsgLeiosVotes { votes } => {
                e.array(2)?;
                e.u32(4)?;
                e.array(votes.len() as u64)?;
                for vote in votes {
                    e.array(4)?;
                    e.u64(vote.slot)?;
                    e.bytes(&vote.eb_hash)?;
                    e.u16(vote.voter_id)?;
                    e.bool(vote.vote_signature)?;
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
        let len = d.array()?;
        let tag = d.u32()?;

        let msg = match tag {
            0 => Message::MsgLeiosNotificationRequestNext,
            1 => {
                let header = WrappedHeader::decode(d, &mut ())?;
                Message::MsgLeiosBlockAnnouncement { header }
            }
            2 => {
                let point = Point::decode(d, &mut ())?;
                let eb_size = d.u32()?;
                Message::MsgLeiosBlockOffer { point, eb_size }
            }
            3 => {
                let point = Point::decode(d, &mut ())?;
                Message::MsgLeiosBlockTxsOffer { point }
            }
            4 => {
                let votes = decode_votes(d)?;
                Message::MsgLeiosVotes { votes }
            }
            5 => Message::MsgDone,
            other => {
                return Err(DecodeError::message(format!(
                    "unknown leios_notify message tag: {other}"
                )))
            }
        };

        // Tolerate (and skip) any trailing elements beyond the fields we
        // read — keeps us forward-compatible with added fields.
        let consumed = match tag {
            0 | 5 => 1,                 // tag only
            1 | 3 | 4 => 2,             // tag + payload
            2 => 3,                     // tag + point + eb_size
            _ => unreachable!(),
        };
        skip_trailing(d, len, consumed)?;
        Ok(msg)
    }
}

/// Skip any unread elements of an array whose declared length is `len`,
/// given we have already consumed `consumed` of them.  Handles both
/// definite-length arrays (skip `len - consumed`) and indefinite-length
/// arrays (skip until the break marker).
fn skip_trailing(
    d: &mut Decoder<'_>,
    len: Option<u64>,
    consumed: u64,
) -> Result<(), DecodeError> {
    match len {
        Some(n) => {
            for _ in consumed..n {
                d.skip()?;
            }
            Ok(())
        }
        None => {
            while d.datatype()? != minicbor::data::Type::Break {
                d.skip()?;
            }
            d.skip()?; // consume the break
            Ok(())
        }
    }
}

/// Decode the inline vote list with a hard cap on entries.
fn decode_votes(d: &mut Decoder<'_>) -> Result<Vec<Vote>, DecodeError> {
    let len = d.array()?;
    match len {
        Some(n) => {
            let n = n as usize;
            if n > MAX_VOTES {
                return Err(DecodeError::message(format!(
                    "vote list has {n} entries, maximum is {MAX_VOTES}"
                )));
            }
            let mut votes = Vec::with_capacity(n);
            for _ in 0..n {
                votes.push(decode_vote(d)?);
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
                        "vote list exceeds maximum of {MAX_VOTES}"
                    )));
                }
                votes.push(decode_vote(d)?);
            }
            Ok(votes)
        }
    }
}

/// Decode a single `vote = [slot, eb_hash, voter_id, vote_signature]`.
fn decode_vote(d: &mut Decoder<'_>) -> Result<Vote, DecodeError> {
    let len = d.array()?;
    let slot = d.u64()?;
    let hash_bytes = d.bytes()?;
    if hash_bytes.len() != 32 {
        return Err(DecodeError::message(format!(
            "vote eb_hash must be 32 bytes, got {}",
            hash_bytes.len()
        )));
    }
    let mut eb_hash = [0u8; 32];
    eb_hash.copy_from_slice(hash_bytes);
    let voter_id = d.u16()?;
    let vote_signature = d.bool()?;
    skip_trailing(d, len, 4)?;
    Ok(Vote {
        slot,
        eb_hash,
        voter_id,
        vote_signature,
    })
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

    /// Decode a lowercase hex string into bytes (test helper).
    fn hex(s: &str) -> Vec<u8> {
        (0..s.len())
            .step_by(2)
            .map(|i| u8::from_str_radix(&s[i..i + 2], 16).unwrap())
            .collect()
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
            eb_size: 16851,
        };
        let decoded = round_trip(&msg);
        match decoded {
            Message::MsgLeiosBlockOffer { point, eb_size } => {
                assert_eq!(
                    point,
                    Point::Specific {
                        slot: 42,
                        hash: test_hash(),
                    }
                );
                assert_eq!(eb_size, 16851);
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
    fn votes_round_trip() {
        let msg = Message::MsgLeiosVotes {
            votes: vec![
                Vote {
                    slot: 100,
                    eb_hash: [0x11; 32],
                    voter_id: 130,
                    vote_signature: true,
                },
                Vote {
                    slot: 200,
                    eb_hash: [0x22; 32],
                    voter_id: 65535,
                    vote_signature: false,
                },
            ],
        };
        let decoded = round_trip(&msg);
        match decoded {
            Message::MsgLeiosVotes { votes } => {
                assert_eq!(votes.len(), 2);
                assert_eq!(votes[0].slot, 100);
                assert_eq!(votes[0].voter_id, 130);
                assert!(votes[0].vote_signature);
                assert_eq!(votes[1].eb_hash, [0x22; 32]);
                assert_eq!(votes[1].voter_id, 65535);
                assert!(!votes[1].vote_signature);
            }
            other => panic!("expected MsgLeiosVotes, got {other:?}"),
        }
    }

    #[test]
    fn votes_empty_round_trip() {
        let msg = Message::MsgLeiosVotes { votes: vec![] };
        let decoded = round_trip(&msg);
        match decoded {
            Message::MsgLeiosVotes { votes } => assert!(votes.is_empty()),
            other => panic!("expected MsgLeiosVotes, got {other:?}"),
        }
    }

    #[test]
    fn done_round_trip() {
        let decoded = round_trip(&Message::MsgDone);
        assert!(matches!(decoded, Message::MsgDone));
    }

    // -- Capture-based vectors (raw frames from leios-node.play.dev.cardano.org) --

    /// Real `msgLeiosBlockOffer` bytes captured off the wire:
    /// `[2, [slot, eb_hash], eb_size]`.
    #[test]
    fn decode_captured_block_offer() {
        let bytes = hex(
            "8302821a0005dfc75820630ee36ae6a20e024a30cb582b3fcd1fd3a1aa0df16c1c7be53fea9ac3f1f70b1941d3",
        );
        let decoded: Message = minicbor::decode(&bytes).unwrap();
        match &decoded {
            Message::MsgLeiosBlockOffer { point, eb_size } => {
                assert_eq!(*eb_size, 0x41d3); // 16851
                match point {
                    Point::Specific { slot, .. } => assert_eq!(*slot, 0x0005_dfc7),
                    other => panic!("expected specific point, got {other:?}"),
                }
            }
            other => panic!("expected MsgLeiosBlockOffer, got {other:?}"),
        }
        // Our encoder reproduces the captured bytes exactly.
        assert_eq!(minicbor::to_vec(&decoded).unwrap(), bytes);
    }

    /// Real `msgLeiosVotes` bytes captured off the wire:
    /// `[4, [[slot, eb_hash, voter_id, true]]]`.
    #[test]
    fn decode_captured_votes() {
        let bytes = hex(
            "820481841a0005dfc75820630ee36ae6a20e024a30cb582b3fcd1fd3a1aa0df16c1c7be53fea9ac3f1f70b1882f5",
        );
        let decoded: Message = minicbor::decode(&bytes).unwrap();
        match &decoded {
            Message::MsgLeiosVotes { votes } => {
                assert_eq!(votes.len(), 1);
                assert_eq!(votes[0].slot, 0x0005_dfc7);
                assert_eq!(votes[0].voter_id, 0x82); // 130
                assert!(votes[0].vote_signature);
            }
            other => panic!("expected MsgLeiosVotes, got {other:?}"),
        }
        // Our encoder reproduces the captured bytes exactly.
        assert_eq!(minicbor::to_vec(&decoded).unwrap(), bytes);
    }

    /// A future revision adds a trailing field to each vote; we must
    /// skip it rather than desync (the bug this whole change fixes).
    #[test]
    fn votes_tolerate_trailing_vote_field() {
        let mut buf = Vec::new();
        let mut e = minicbor::Encoder::new(&mut buf);
        e.array(2).unwrap();
        e.u32(4).unwrap();
        e.array(1).unwrap();
        e.array(5).unwrap(); // 5-element vote: 4 known + 1 future field
        e.u64(7).unwrap();
        e.bytes(&[0xAB; 32]).unwrap();
        e.u16(3).unwrap();
        e.bool(true).unwrap();
        e.u64(999).unwrap(); // trailing field
        let decoded: Message = minicbor::decode(&buf).unwrap();
        match decoded {
            Message::MsgLeiosVotes { votes } => {
                assert_eq!(votes.len(), 1);
                assert_eq!(votes[0].slot, 7);
                assert_eq!(votes[0].voter_id, 3);
            }
            other => panic!("expected MsgLeiosVotes, got {other:?}"),
        }
    }

    /// A trailing field on the block offer is skipped too.
    #[test]
    fn block_offer_tolerates_trailing_field() {
        let mut buf = Vec::new();
        let mut e = minicbor::Encoder::new(&mut buf);
        e.array(4).unwrap(); // [2, point, eb_size, future]
        e.u32(2).unwrap();
        e.array(2).unwrap();
        e.u64(5).unwrap();
        e.bytes(&[0u8; 32]).unwrap();
        e.u32(42).unwrap();
        e.u64(123).unwrap(); // trailing field
        let decoded: Message = minicbor::decode(&buf).unwrap();
        match decoded {
            Message::MsgLeiosBlockOffer { eb_size, .. } => assert_eq!(eb_size, 42),
            other => panic!("expected MsgLeiosBlockOffer, got {other:?}"),
        }
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
        // MsgLeiosBlockOffer with a 16-byte point hash — fails in Point.
        let mut buf = Vec::new();
        let mut e = minicbor::Encoder::new(&mut buf);
        e.array(3).unwrap();
        e.u32(2).unwrap();
        e.array(2).unwrap();
        e.u64(0).unwrap();
        e.bytes(&[0u8; 16]).unwrap(); // 16 bytes, not 32
        e.u32(0).unwrap();

        let result: Result<Message, _> = minicbor::decode(&buf);
        assert!(result.is_err());
    }

    #[test]
    fn votes_exceeds_max_fails() {
        let mut buf = Vec::new();
        let mut e = minicbor::Encoder::new(&mut buf);
        e.array(2).unwrap();
        e.u32(4).unwrap();
        let n = MAX_VOTES + 1;
        e.array(n as u64).unwrap();
        for i in 0..n {
            e.array(4).unwrap();
            e.u64(i as u64).unwrap();
            e.bytes(&[0u8; 32]).unwrap();
            e.u16(1).unwrap();
            e.bool(true).unwrap();
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
            eb_size: 7,
        };
        let encoded = minicbor::to_vec(&msg).unwrap();
        let truncated = &encoded[..3];
        let result: Result<Message, _> = minicbor::decode(truncated);
        assert!(result.is_err());
    }
}
