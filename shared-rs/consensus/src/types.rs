//! Cardano consensus value types.
//!
//! Protocol identity types — what a "block" is named on the chain —
//! not transport types. Wire codecs live with the type because every
//! consumer must agree on the on-wire encoding, but the type itself
//! carries no I/O.

use std::fmt;

use minicbor::decode::Error as DecodeError;
use minicbor::encode::Error as EncodeError;
use minicbor::{Decoder, Encoder};

/// A point on the chain: either the genesis (origin) or a specific slot+hash.
///
/// Wire format:
///   origin   = []                    (empty array)
///   specific = [slotNo, headerHash]  (2-element array)
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Point {
    Origin,
    Specific { slot: u64, hash: [u8; 32] },
}

impl fmt::Display for Point {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Point::Origin => write!(f, "origin"),
            Point::Specific { slot, hash } => {
                write!(f, "{}/{}", slot, hex_prefix(hash))
            }
        }
    }
}

impl minicbor::Encode<()> for Point {
    fn encode<W: minicbor::encode::Write>(
        &self,
        e: &mut Encoder<W>,
        _ctx: &mut (),
    ) -> Result<(), EncodeError<W::Error>> {
        match self {
            Point::Origin => {
                e.array(0)?;
            }
            Point::Specific { slot, hash } => {
                e.array(2)?;
                e.u64(*slot)?;
                e.bytes(hash)?;
            }
        }
        Ok(())
    }
}

impl<'a> minicbor::Decode<'a, ()> for Point {
    fn decode(d: &mut Decoder<'a>, _ctx: &mut ()) -> Result<Self, DecodeError> {
        let len = d.array()?;
        match len {
            Some(0) => Ok(Point::Origin),
            None => {
                // Indefinite-length array — check if immediately closed (origin)
                // or has elements (specific).
                if d.datatype()? == minicbor::data::Type::Break {
                    d.skip()?; // consume the break
                    return Ok(Point::Origin);
                }
                let slot = d.u64()?;
                let hash_bytes = d.bytes()?;
                if hash_bytes.len() != 32 {
                    return Err(DecodeError::message(format!(
                        "point hash must be 32 bytes, got {}",
                        hash_bytes.len()
                    )));
                }
                let mut hash = [0u8; 32];
                hash.copy_from_slice(hash_bytes);
                // Consume the break marker.
                if d.datatype()? == minicbor::data::Type::Break {
                    d.skip()?;
                }
                Ok(Point::Specific { slot, hash })
            }
            Some(2) => {
                let slot = d.u64()?;
                let hash_bytes = d.bytes()?;
                if hash_bytes.len() != 32 {
                    return Err(DecodeError::message(format!(
                        "point hash must be 32 bytes, got {}",
                        hash_bytes.len()
                    )));
                }
                let mut hash = [0u8; 32];
                hash.copy_from_slice(hash_bytes);
                Ok(Point::Specific { slot, hash })
            }
            Some(other) => Err(DecodeError::message(format!(
                "expected point array of length 0 or 2, got {other}"
            ))),
        }
    }
}

/// Chain tip: a point plus the block number.
///
/// Wire format: [point, blockNo]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Tip {
    pub point: Point,
    pub block_no: u64,
}

impl fmt::Display for Tip {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}@block#{}", self.point, self.block_no)
    }
}

impl minicbor::Encode<()> for Tip {
    fn encode<W: minicbor::encode::Write>(
        &self,
        e: &mut Encoder<W>,
        _ctx: &mut (),
    ) -> Result<(), EncodeError<W::Error>> {
        e.array(2)?;
        self.point.encode(e, &mut ())?;
        e.u64(self.block_no)?;
        Ok(())
    }
}

impl<'a> minicbor::Decode<'a, ()> for Tip {
    fn decode(d: &mut Decoder<'a>, _ctx: &mut ()) -> Result<Self, DecodeError> {
        let _len = d.array()?;
        let point = Point::decode(d, &mut ())?;
        let block_no = d.u64()?;
        Ok(Tip { point, block_no })
    }
}

/// A Leios vote, delivered inline (no offer/fetch round-trip).
///
/// Mirrors the CIP-0164 prototype wire shape
/// (`vote = [slot, eb_hash, voter_id: word16, vote_signature: bool]`):
///
/// - `slot` — the slot at which the endorser block was announced (its
///   election id); votes can arrive before the local node has seen the
///   EB body, so the slot is needed to place the vote in its pipeline.
/// - `eb_hash` — the endorser block being voted on.
/// - `voter_id` — compact voter index; resolves to a registered pool
///   via the deterministic voter registry (see `committee.rs`).
/// - `vote_signature` — mocked in the prototype (a `bool`); a real
///   deployment carries a BLS signature here.
///
/// The CBOR codec lives in the network I/O layer (this crate stays
/// format-agnostic); this is the logical value every consumer agrees on.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Vote {
    pub slot: u64,
    pub eb_hash: [u8; 32],
    pub voter_id: u16,
    pub vote_signature: bool,
}

/// Hex-encode the first 8 bytes of a hash for display.
pub(crate) fn hex_prefix(hash: &[u8; 32]) -> String {
    hash.iter()
        .take(8)
        .map(|b| format!("{b:02x}"))
        .collect::<String>()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn point_origin_round_trip() {
        let point = Point::Origin;
        let encoded = minicbor::to_vec(&point).unwrap();
        assert_eq!(encoded, &[0x80]); // definite empty array
        let decoded: Point = minicbor::decode(&encoded).unwrap();
        assert_eq!(decoded, point);
    }

    #[test]
    fn point_specific_round_trip() {
        let point = Point::Specific {
            slot: 12345,
            hash: [0xAB; 32],
        };
        let encoded = minicbor::to_vec(&point).unwrap();
        let decoded: Point = minicbor::decode(&encoded).unwrap();
        assert_eq!(decoded, point);
    }

    #[test]
    fn point_specific_rejects_wrong_hash_length() {
        // Manually constructed [slot, 16-byte-hash] should fail.
        let mut bytes = Vec::new();
        let mut e = Encoder::new(&mut bytes);
        e.array(2).unwrap();
        e.u64(1).unwrap();
        e.bytes(&[0u8; 16]).unwrap();
        assert!(minicbor::decode::<Point>(&bytes).is_err());
    }

    #[test]
    fn point_display() {
        assert_eq!(format!("{}", Point::Origin), "origin");
        let p = Point::Specific {
            slot: 42,
            hash: [0xAB; 32],
        };
        assert_eq!(format!("{p}"), "42/abababababababab");
    }
}
