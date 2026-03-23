//! CBOR encoding for BlockFetch messages.
//!
//! Wire format (from spec section 3.6.4):
//!
//!   msgRequestRange = [0, point, point]
//!   msgClientDone   = [1]
//!   msgStartBatch   = [2]
//!   msgNoBlocks     = [3]
//!   msgBlock        = [4, block]
//!   msgBatchDone    = [5]

use minicbor::decode::Error as DecodeError;
use minicbor::encode::Error as EncodeError;
use minicbor::{Decoder, Encoder};

use super::Message;
use crate::types::{BlockBody, Point};

impl minicbor::Encode<()> for Message {
    fn encode<W: minicbor::encode::Write>(
        &self,
        e: &mut Encoder<W>,
        _ctx: &mut (),
    ) -> Result<(), EncodeError<W::Error>> {
        match self {
            Message::MsgRequestRange { from, to } => {
                e.array(3)?;
                e.u32(0)?;
                minicbor::Encode::encode(from, e, &mut ())?;
                minicbor::Encode::encode(to, e, &mut ())?;
            }
            Message::MsgClientDone => {
                e.array(1)?;
                e.u32(1)?;
            }
            Message::MsgStartBatch => {
                e.array(1)?;
                e.u32(2)?;
            }
            Message::MsgNoBlocks => {
                e.array(1)?;
                e.u32(3)?;
            }
            Message::MsgBlock { body } => {
                e.array(2)?;
                e.u32(4)?;
                minicbor::Encode::encode(body, e, &mut ())?;
            }
            Message::MsgBatchDone => {
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
            0 => {
                let from = Point::decode(d, &mut ())?;
                let to = Point::decode(d, &mut ())?;
                Ok(Message::MsgRequestRange { from, to })
            }
            1 => Ok(Message::MsgClientDone),
            2 => Ok(Message::MsgStartBatch),
            3 => Ok(Message::MsgNoBlocks),
            4 => {
                let body = BlockBody::decode(d, &mut ())?;
                Ok(Message::MsgBlock { body })
            }
            5 => Ok(Message::MsgBatchDone),
            other => Err(DecodeError::message(format!(
                "unknown blockfetch message tag: {other}"
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

    #[test]
    fn request_range_round_trip() {
        let msg = Message::MsgRequestRange {
            from: Point::Specific {
                slot: 10,
                hash: [0xaa; 32],
            },
            to: Point::Specific {
                slot: 20,
                hash: [0xbb; 32],
            },
        };
        let decoded = round_trip(&msg);
        match decoded {
            Message::MsgRequestRange { from, to } => {
                assert_eq!(
                    from,
                    Point::Specific {
                        slot: 10,
                        hash: [0xaa; 32],
                    }
                );
                assert_eq!(
                    to,
                    Point::Specific {
                        slot: 20,
                        hash: [0xbb; 32],
                    }
                );
            }
            other => panic!("expected RequestRange, got {other:?}"),
        }
    }

    #[test]
    fn client_done_round_trip() {
        let decoded = round_trip(&Message::MsgClientDone);
        assert!(matches!(decoded, Message::MsgClientDone));
    }

    #[test]
    fn start_batch_round_trip() {
        let decoded = round_trip(&Message::MsgStartBatch);
        assert!(matches!(decoded, Message::MsgStartBatch));
    }

    #[test]
    fn no_blocks_round_trip() {
        let decoded = round_trip(&Message::MsgNoBlocks);
        assert!(matches!(decoded, Message::MsgNoBlocks));
    }

    #[test]
    fn block_round_trip() {
        let body = BlockBody(vec![0xd8, 0x18, 0x43, 0x01, 0x02, 0x03]);
        let msg = Message::MsgBlock { body: body.clone() };
        let decoded = round_trip(&msg);
        match decoded {
            Message::MsgBlock { body: b } => assert_eq!(b, body),
            other => panic!("expected Block, got {other:?}"),
        }
    }

    #[test]
    fn batch_done_round_trip() {
        let decoded = round_trip(&Message::MsgBatchDone);
        assert!(matches!(decoded, Message::MsgBatchDone));
    }

    #[test]
    fn unknown_tag_fails() {
        let bad = &[0x81, 0x18, 0x63]; // [99]
        let result: Result<Message, _> = minicbor::decode(bad);
        assert!(result.is_err());
    }

    #[test]
    fn truncated_request_range_fails() {
        let msg = Message::MsgRequestRange {
            from: Point::Origin,
            to: Point::Origin,
        };
        let encoded = minicbor::to_vec(&msg).unwrap();
        let truncated = &encoded[..3];
        let result: Result<Message, _> = minicbor::decode(truncated);
        assert!(result.is_err());
    }

    #[test]
    fn decode_indefinite_outer_array() {
        // [2] as indefinite: 0x9f 0x02 0xff
        let cbor = &[0x9f, 0x02, 0xff];
        let decoded: Message = minicbor::decode(cbor).unwrap();
        assert!(matches!(decoded, Message::MsgStartBatch));
    }
}
