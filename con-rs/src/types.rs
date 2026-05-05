//! Cardano consensus value types shared between sim-rs and net-rs.
//!
//! These are protocol identity types — what a "block" is named on the
//! chain — not transport types. Wire codecs live with the type because
//! both consumers must agree on the on-wire encoding, but the type
//! itself carries no I/O.

use std::fmt;

use minicbor::decode::Error as DecodeError;
use minicbor::encode::Error as EncodeError;
use minicbor::{Decoder, Encoder};

/// A point on the chain: either the genesis (origin) or a specific slot+hash.
///
/// Wire format:
///   origin   = []                    (empty array)
///   specific = [slotNo, headerHash]  (2-element array)
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
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
