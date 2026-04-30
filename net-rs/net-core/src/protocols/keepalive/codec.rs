//! CBOR encoding for KeepAlive messages.
//!
//! Wire format:
//!   msgKeepAlive         = [0, word16]
//!   msgKeepAliveResponse = [1, word16]
//!   msgDone              = [2]

use minicbor::decode::Error as DecodeError;
use minicbor::encode::Error as EncodeError;
use minicbor::{Decoder, Encoder};

use super::Message;

impl minicbor::Encode<()> for Message {
    fn encode<W: minicbor::encode::Write>(
        &self,
        e: &mut Encoder<W>,
        _ctx: &mut (),
    ) -> Result<(), EncodeError<W::Error>> {
        match self {
            Message::MsgKeepAlive { cookie } => {
                e.array(2)?;
                e.u32(0)?;
                e.u16(*cookie)?;
            }
            Message::MsgKeepAliveResponse { cookie } => {
                e.array(2)?;
                e.u32(1)?;
                e.u16(*cookie)?;
            }
            Message::MsgDone => {
                e.array(1)?;
                e.u32(2)?;
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
                let cookie = d.u16()?;
                Ok(Message::MsgKeepAlive { cookie })
            }
            1 => {
                let cookie = d.u16()?;
                Ok(Message::MsgKeepAliveResponse { cookie })
            }
            2 => Ok(Message::MsgDone),
            other => Err(DecodeError::message(format!(
                "unknown keepalive message tag: {other}"
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
    fn keep_alive_round_trip() {
        let msg = Message::MsgKeepAlive { cookie: 12345 };
        assert_eq!(round_trip(&msg), msg);
    }

    #[test]
    fn keep_alive_response_round_trip() {
        let msg = Message::MsgKeepAliveResponse { cookie: 54321 };
        assert_eq!(round_trip(&msg), msg);
    }

    #[test]
    fn done_round_trip() {
        let msg = Message::MsgDone;
        assert_eq!(round_trip(&msg), msg);
    }

    #[test]
    fn unknown_tag_fails() {
        let bad = &[0x81, 0x18, 0x63]; // [99]
        let result: Result<Message, _> = minicbor::decode(bad);
        assert!(result.is_err());
    }

    #[test]
    fn decode_indefinite_outer_array() {
        // [0, 42] as indefinite: 0x9f 0x00 0x18 0x2a 0xff
        let cbor = &[0x9f, 0x00, 0x18, 0x2a, 0xff];
        let decoded: Message = minicbor::decode(cbor).unwrap();
        assert_eq!(decoded, Message::MsgKeepAlive { cookie: 42 });
    }
}
