//! CBOR encoding for ChainSync messages.
//!
//! Wire format (from spec section 3.6.2):
//!
//!   msgRequestNext       = [0]
//!   msgAwaitReply        = [1]
//!   msgRollForward       = [2, header, tip]
//!   msgRollBackward      = [3, point, tip]
//!   msgFindIntersect     = [4, points]
//!   msgIntersectFound    = [5, point, tip]
//!   msgIntersectNotFound = [6, tip]
//!   chainSyncMsgDone     = [7]

use minicbor::decode::Error as DecodeError;
use minicbor::encode::Error as EncodeError;
use minicbor::{Decoder, Encoder};

use super::Message;
use crate::types::{self, Point, Tip, WrappedHeader};

impl minicbor::Encode<()> for Message {
    fn encode<W: minicbor::encode::Write>(
        &self,
        e: &mut Encoder<W>,
        _ctx: &mut (),
    ) -> Result<(), EncodeError<W::Error>> {
        match self {
            Message::MsgRequestNext => {
                e.array(1)?;
                e.u32(0)?;
            }
            Message::MsgAwaitReply => {
                e.array(1)?;
                e.u32(1)?;
            }
            Message::MsgRollForward { header, tip } => {
                e.array(3)?;
                e.u32(2)?;
                minicbor::Encode::encode(header, e, &mut ())?;
                minicbor::Encode::encode(tip, e, &mut ())?;
            }
            Message::MsgRollBackward { point, tip } => {
                e.array(3)?;
                e.u32(3)?;
                minicbor::Encode::encode(point, e, &mut ())?;
                minicbor::Encode::encode(tip, e, &mut ())?;
            }
            Message::MsgFindIntersect { points } => {
                e.array(2)?;
                e.u32(4)?;
                types::encode_points(e, points)?;
            }
            Message::MsgIntersectFound { point, tip } => {
                e.array(3)?;
                e.u32(5)?;
                minicbor::Encode::encode(point, e, &mut ())?;
                minicbor::Encode::encode(tip, e, &mut ())?;
            }
            Message::MsgIntersectNotFound { tip } => {
                e.array(2)?;
                e.u32(6)?;
                minicbor::Encode::encode(tip, e, &mut ())?;
            }
            Message::MsgDone => {
                e.array(1)?;
                e.u32(7)?;
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
            0 => Ok(Message::MsgRequestNext),
            1 => Ok(Message::MsgAwaitReply),
            2 => {
                let header = WrappedHeader::decode(d, &mut ())?;
                let tip = Tip::decode(d, &mut ())?;
                Ok(Message::MsgRollForward { header, tip })
            }
            3 => {
                let point = Point::decode(d, &mut ())?;
                let tip = Tip::decode(d, &mut ())?;
                Ok(Message::MsgRollBackward { point, tip })
            }
            4 => {
                let points = types::decode_points(d)?;
                Ok(Message::MsgFindIntersect { points })
            }
            5 => {
                let point = Point::decode(d, &mut ())?;
                let tip = Tip::decode(d, &mut ())?;
                Ok(Message::MsgIntersectFound { point, tip })
            }
            6 => {
                let tip = Tip::decode(d, &mut ())?;
                Ok(Message::MsgIntersectNotFound { tip })
            }
            7 => Ok(Message::MsgDone),
            other => Err(DecodeError::message(format!(
                "unknown chainsync message tag: {other}"
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

    fn sample_tip() -> Tip {
        Tip {
            point: Point::Specific {
                slot: 42,
                hash: [0xab; 32],
            },
            block_no: 100,
        }
    }

    #[test]
    fn request_next_round_trip() {
        let msg = Message::MsgRequestNext;
        let decoded = round_trip(&msg);
        assert!(matches!(decoded, Message::MsgRequestNext));
    }

    #[test]
    fn await_reply_round_trip() {
        let msg = Message::MsgAwaitReply;
        let decoded = round_trip(&msg);
        assert!(matches!(decoded, Message::MsgAwaitReply));
    }

    #[test]
    fn roll_forward_round_trip() {
        let header =
            WrappedHeader::opaque(vec![0x82, 0x06, 0xd8, 0x18, 0x44, 0xde, 0xad, 0xbe, 0xef]);
        let msg = Message::MsgRollForward {
            header: header.clone(),
            tip: sample_tip(),
        };
        let decoded = round_trip(&msg);
        match decoded {
            Message::MsgRollForward { header: h, tip: t } => {
                assert_eq!(h, header);
                assert_eq!(t, sample_tip());
            }
            other => panic!("expected RollForward, got {other:?}"),
        }
    }

    #[test]
    fn roll_backward_round_trip() {
        let msg = Message::MsgRollBackward {
            point: Point::Origin,
            tip: sample_tip(),
        };
        let decoded = round_trip(&msg);
        match decoded {
            Message::MsgRollBackward { point, tip } => {
                assert_eq!(point, Point::Origin);
                assert_eq!(tip, sample_tip());
            }
            other => panic!("expected RollBackward, got {other:?}"),
        }
    }

    #[test]
    fn find_intersect_round_trip() {
        let points = vec![
            Point::Specific {
                slot: 100,
                hash: [0x01; 32],
            },
            Point::Origin,
        ];
        let msg = Message::MsgFindIntersect {
            points: points.clone(),
        };
        let decoded = round_trip(&msg);
        match decoded {
            Message::MsgFindIntersect { points: p } => {
                assert_eq!(p, points);
            }
            other => panic!("expected FindIntersect, got {other:?}"),
        }
    }

    #[test]
    fn find_intersect_empty_round_trip() {
        let msg = Message::MsgFindIntersect { points: vec![] };
        let decoded = round_trip(&msg);
        match decoded {
            Message::MsgFindIntersect { points } => {
                assert!(points.is_empty());
            }
            other => panic!("expected FindIntersect, got {other:?}"),
        }
    }

    #[test]
    fn intersect_found_round_trip() {
        let msg = Message::MsgIntersectFound {
            point: Point::Specific {
                slot: 50,
                hash: [0xcc; 32],
            },
            tip: sample_tip(),
        };
        let decoded = round_trip(&msg);
        match decoded {
            Message::MsgIntersectFound { point, tip } => {
                assert_eq!(
                    point,
                    Point::Specific {
                        slot: 50,
                        hash: [0xcc; 32],
                    }
                );
                assert_eq!(tip, sample_tip());
            }
            other => panic!("expected IntersectFound, got {other:?}"),
        }
    }

    #[test]
    fn intersect_not_found_round_trip() {
        let msg = Message::MsgIntersectNotFound { tip: sample_tip() };
        let decoded = round_trip(&msg);
        match decoded {
            Message::MsgIntersectNotFound { tip } => {
                assert_eq!(tip, sample_tip());
            }
            other => panic!("expected IntersectNotFound, got {other:?}"),
        }
    }

    #[test]
    fn done_round_trip() {
        let msg = Message::MsgDone;
        let decoded = round_trip(&msg);
        assert!(matches!(decoded, Message::MsgDone));
    }

    #[test]
    fn unknown_tag_fails() {
        // CBOR array [99]
        let bad = &[0x81, 0x18, 0x63];
        let result: Result<Message, _> = minicbor::decode(bad);
        assert!(result.is_err());
    }

    #[test]
    fn truncated_roll_forward_fails() {
        // Encode a valid RollForward then truncate.
        let msg = Message::MsgRollForward {
            header: WrappedHeader::opaque(vec![0x80]),
            tip: sample_tip(),
        };
        let encoded = minicbor::to_vec(&msg).unwrap();
        let truncated = &encoded[..5];
        let result: Result<Message, _> = minicbor::decode(truncated);
        assert!(result.is_err());
    }

    #[test]
    fn decode_indefinite_outer_array() {
        // Manually construct [0] as indefinite-length: 0x9f 0x00 0xff
        let cbor = &[0x9f, 0x00, 0xff];
        let decoded: Message = minicbor::decode(cbor).unwrap();
        assert!(matches!(decoded, Message::MsgRequestNext));
    }
}
