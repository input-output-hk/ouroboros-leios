//! CBOR encoding for PeerSharing messages.
//!
//! Wire format (from spec section 10.5):
//!
//!   msgShareRequest = [0, word8]
//!   msgSharePeers   = [1, peerAddresses]
//!   msgDone         = [2]
//!
//!   peerAddress = [0, word32, portNumber]                             ; IPv4
//!               / [1, word32, word32, word32, word32, portNumber]     ; IPv6
//!   portNumber  = word16

use minicbor::decode::Error as DecodeError;
use minicbor::encode::Error as EncodeError;
use minicbor::{Decoder, Encoder};

use super::{Message, PeerAddress, MAX_PEERS};

use std::net::{Ipv4Addr, Ipv6Addr};

// --- PeerAddress encode/decode ---

impl minicbor::Encode<()> for PeerAddress {
    fn encode<W: minicbor::encode::Write>(
        &self,
        e: &mut Encoder<W>,
        _ctx: &mut (),
    ) -> Result<(), EncodeError<W::Error>> {
        match self {
            PeerAddress::IPv4 { addr, port } => {
                e.array(3)?;
                e.u32(0)?;
                e.u32(u32::from(*addr))?;
                e.u16(*port)?;
            }
            PeerAddress::IPv6 { addr, port } => {
                e.array(6)?;
                e.u32(1)?;
                let octets = addr.octets();
                e.u32(u32::from_be_bytes([
                    octets[0], octets[1], octets[2], octets[3],
                ]))?;
                e.u32(u32::from_be_bytes([
                    octets[4], octets[5], octets[6], octets[7],
                ]))?;
                e.u32(u32::from_be_bytes([
                    octets[8], octets[9], octets[10], octets[11],
                ]))?;
                e.u32(u32::from_be_bytes([
                    octets[12], octets[13], octets[14], octets[15],
                ]))?;
                e.u16(*port)?;
            }
        }
        Ok(())
    }
}

impl<'a> minicbor::Decode<'a, ()> for PeerAddress {
    fn decode(d: &mut Decoder<'a>, _ctx: &mut ()) -> Result<Self, DecodeError> {
        let _len = d.array()?;
        let tag = d.u32()?;
        match tag {
            0 => {
                let ip = d.u32()?;
                let port = d.u16()?;
                Ok(PeerAddress::IPv4 {
                    addr: Ipv4Addr::from(ip),
                    port,
                })
            }
            1 => {
                let a = d.u32()?;
                let b = d.u32()?;
                let c = d.u32()?;
                let dd = d.u32()?;
                let port = d.u16()?;
                let mut octets = [0u8; 16];
                octets[0..4].copy_from_slice(&a.to_be_bytes());
                octets[4..8].copy_from_slice(&b.to_be_bytes());
                octets[8..12].copy_from_slice(&c.to_be_bytes());
                octets[12..16].copy_from_slice(&dd.to_be_bytes());
                Ok(PeerAddress::IPv6 {
                    addr: Ipv6Addr::from(octets),
                    port,
                })
            }
            other => Err(DecodeError::message(format!(
                "unknown peer address tag: {other}"
            ))),
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
            Message::MsgShareRequest { amount } => {
                e.array(2)?;
                e.u32(0)?;
                e.u8(*amount)?;
            }
            Message::MsgSharePeers { peers } => {
                e.array(2)?;
                e.u32(1)?;
                e.array(peers.len() as u64)?;
                for peer in peers {
                    peer.encode(e, &mut ())?;
                }
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
                let amount = d.u8()?;
                Ok(Message::MsgShareRequest { amount })
            }
            1 => {
                let len = d.array()?;
                let peers = match len {
                    Some(n) => {
                        let n = n as usize;
                        if n > MAX_PEERS {
                            return Err(DecodeError::message(format!(
                                "peer list has {n} entries, maximum is {MAX_PEERS}"
                            )));
                        }
                        let mut peers = Vec::with_capacity(n);
                        for _ in 0..n {
                            peers.push(PeerAddress::decode(d, &mut ())?);
                        }
                        peers
                    }
                    None => {
                        let mut peers = Vec::new();
                        loop {
                            if d.datatype()? == minicbor::data::Type::Break {
                                d.skip()?;
                                break;
                            }
                            if peers.len() >= MAX_PEERS {
                                return Err(DecodeError::message(format!(
                                    "peer list exceeds maximum of {MAX_PEERS}"
                                )));
                            }
                            peers.push(PeerAddress::decode(d, &mut ())?);
                        }
                        peers
                    }
                };
                Ok(Message::MsgSharePeers { peers })
            }
            2 => Ok(Message::MsgDone),
            other => Err(DecodeError::message(format!(
                "unknown peersharing message tag: {other}"
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
    fn share_request_round_trip() {
        let msg = Message::MsgShareRequest { amount: 10 };
        let decoded = round_trip(&msg);
        match decoded {
            Message::MsgShareRequest { amount } => assert_eq!(amount, 10),
            other => panic!("expected MsgShareRequest, got {other:?}"),
        }
    }

    #[test]
    fn share_peers_ipv4_round_trip() {
        let msg = Message::MsgSharePeers {
            peers: vec![PeerAddress::IPv4 {
                addr: Ipv4Addr::new(192, 168, 1, 100),
                port: 3001,
            }],
        };
        let decoded = round_trip(&msg);
        match decoded {
            Message::MsgSharePeers { peers } => {
                assert_eq!(peers.len(), 1);
                match &peers[0] {
                    PeerAddress::IPv4 { addr, port } => {
                        assert_eq!(*addr, Ipv4Addr::new(192, 168, 1, 100));
                        assert_eq!(*port, 3001);
                    }
                    other => panic!("expected IPv4, got {other:?}"),
                }
            }
            other => panic!("expected MsgSharePeers, got {other:?}"),
        }
    }

    #[test]
    fn share_peers_ipv6_round_trip() {
        let msg = Message::MsgSharePeers {
            peers: vec![PeerAddress::IPv6 {
                addr: Ipv6Addr::new(0x2001, 0xdb8, 0, 0, 0, 0, 0, 1),
                port: 3001,
            }],
        };
        let decoded = round_trip(&msg);
        match decoded {
            Message::MsgSharePeers { peers } => {
                assert_eq!(peers.len(), 1);
                match &peers[0] {
                    PeerAddress::IPv6 { addr, port } => {
                        assert_eq!(*addr, Ipv6Addr::new(0x2001, 0xdb8, 0, 0, 0, 0, 0, 1));
                        assert_eq!(*port, 3001);
                    }
                    other => panic!("expected IPv6, got {other:?}"),
                }
            }
            other => panic!("expected MsgSharePeers, got {other:?}"),
        }
    }

    #[test]
    fn share_peers_empty_round_trip() {
        let msg = Message::MsgSharePeers { peers: vec![] };
        let decoded = round_trip(&msg);
        match decoded {
            Message::MsgSharePeers { peers } => assert!(peers.is_empty()),
            other => panic!("expected MsgSharePeers, got {other:?}"),
        }
    }

    #[test]
    fn share_peers_mixed_round_trip() {
        let msg = Message::MsgSharePeers {
            peers: vec![
                PeerAddress::IPv4 {
                    addr: Ipv4Addr::new(10, 0, 0, 1),
                    port: 3001,
                },
                PeerAddress::IPv6 {
                    addr: Ipv6Addr::LOCALHOST,
                    port: 3002,
                },
            ],
        };
        let decoded = round_trip(&msg);
        match decoded {
            Message::MsgSharePeers { peers } => {
                assert_eq!(peers.len(), 2);
                assert!(matches!(peers[0], PeerAddress::IPv4 { .. }));
                assert!(matches!(peers[1], PeerAddress::IPv6 { .. }));
            }
            other => panic!("expected MsgSharePeers, got {other:?}"),
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
        let msg = Message::MsgShareRequest { amount: 5 };
        let encoded = minicbor::to_vec(&msg).unwrap();
        let truncated = &encoded[..1];
        let result: Result<Message, _> = minicbor::decode(truncated);
        assert!(result.is_err());
    }

    #[test]
    fn decode_indefinite_outer_array() {
        // MsgDone [2] as indefinite: 0x9f 0x02 0xff
        let cbor = &[0x9f, 0x02, 0xff];
        let decoded: Message = minicbor::decode(cbor).unwrap();
        assert!(matches!(decoded, Message::MsgDone));
    }

    #[test]
    fn unknown_peer_address_tag_fails() {
        // MsgSharePeers with a bad address tag.
        let mut buf = Vec::new();
        let mut e = minicbor::Encoder::new(&mut buf);
        e.array(2).unwrap();
        e.u32(1).unwrap();
        e.array(1).unwrap(); // 1 peer
        e.array(3).unwrap(); // looks like IPv4 but...
        e.u32(99).unwrap(); // bad tag
        e.u32(0).unwrap();
        e.u16(0).unwrap();

        let result: Result<Message, _> = minicbor::decode(&buf);
        assert!(result.is_err());
    }

    #[test]
    fn peer_address_display() {
        let v4 = PeerAddress::IPv4 {
            addr: Ipv4Addr::new(1, 2, 3, 4),
            port: 3001,
        };
        assert_eq!(format!("{v4}"), "1.2.3.4:3001");

        let v6 = PeerAddress::IPv6 {
            addr: Ipv6Addr::new(0x2001, 0xdb8, 0, 0, 0, 0, 0, 1),
            port: 3001,
        };
        assert_eq!(format!("{v6}"), "[2001:db8::1]:3001");
    }
}
