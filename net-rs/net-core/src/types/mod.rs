//! Shared Cardano types used across mini-protocols.
//!
//! - `Point` and `Tip`: chain position types used by ChainSync and BlockFetch.
//! - `WrappedHeader` (in `header`): era-tagged block headers with optional parsed fields.
//! - `BlockBody` (in `block`): raw block bodies with optional Leios metadata.

mod block;
mod header;

pub use block::{BlockBody, LeiosBlockInfo};
pub use header::{HeaderInfo, WrappedHeader};

use std::fmt;

use minicbor::decode::Error as DecodeError;
use minicbor::encode::Error as EncodeError;
use minicbor::{Decode, Decoder, Encode, Encoder};

/// Maximum number of points in a FindIntersect message.
pub const MAX_POINTS: usize = 2048;

/// Maximum header size (matches ChainSync per-state size limit).
pub const MAX_HEADER_SIZE: usize = 65_535;

/// Maximum block body size (matches BlockFetch StStreaming size limit).
pub const MAX_BLOCK_SIZE: usize = 2_500_000;

// --- Point ---

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

// --- Tip ---

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

// --- Helpers ---

/// Hex-encode the first 8 bytes of a hash for display.
fn hex_prefix(hash: &[u8; 32]) -> String {
    hash.iter()
        .take(8)
        .map(|b| format!("{b:02x}"))
        .collect::<String>()
}

/// Decode an array of points, handling both definite and indefinite length.
/// Enforces MAX_POINTS to prevent unbounded allocation.
pub fn decode_points(d: &mut Decoder<'_>) -> Result<Vec<Point>, DecodeError> {
    let len = d.array()?;
    match len {
        Some(n) => {
            if n as usize > MAX_POINTS {
                return Err(DecodeError::message(format!(
                    "points array has {n} entries, maximum is {MAX_POINTS}"
                )));
            }
            let mut points = Vec::with_capacity(n as usize);
            for _ in 0..n {
                points.push(Point::decode(d, &mut ())?);
            }
            Ok(points)
        }
        None => {
            // Indefinite-length array.
            let mut points = Vec::new();
            loop {
                if d.datatype()? == minicbor::data::Type::Break {
                    d.skip()?; // consume the break
                    break;
                }
                if points.len() >= MAX_POINTS {
                    return Err(DecodeError::message(format!(
                        "points array exceeds maximum of {MAX_POINTS}"
                    )));
                }
                points.push(Point::decode(d, &mut ())?);
            }
            Ok(points)
        }
    }
}

/// Encode an array of points as a definite-length CBOR array.
pub fn encode_points<W: minicbor::encode::Write>(
    e: &mut Encoder<W>,
    points: &[Point],
) -> Result<(), EncodeError<W::Error>> {
    e.array(points.len() as u64)?;
    for point in points {
        point.encode(e, &mut ())?;
    }
    Ok(())
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
    fn point_origin_indefinite_decode() {
        // Indefinite-length empty array: 0x9f 0xff
        let cbor = &[0x9f, 0xff];
        let decoded: Point = minicbor::decode(cbor).unwrap();
        assert_eq!(decoded, Point::Origin);
    }

    #[test]
    fn point_specific_round_trip() {
        let hash = [0xab; 32];
        let point = Point::Specific { slot: 12345, hash };
        let encoded = minicbor::to_vec(&point).unwrap();
        let decoded: Point = minicbor::decode(&encoded).unwrap();
        assert_eq!(decoded, point);
    }

    #[test]
    fn point_bad_hash_length() {
        // Encode a point with a 16-byte hash (too short).
        let mut buf = Vec::new();
        let mut e = minicbor::Encoder::new(&mut buf);
        e.array(2).unwrap();
        e.u64(100).unwrap();
        e.bytes(&[0u8; 16]).unwrap();
        let result: Result<Point, _> = minicbor::decode(&buf);
        assert!(result.is_err());
    }

    #[test]
    fn point_display() {
        assert_eq!(format!("{}", Point::Origin), "origin");
        let hash = [0xab; 32];
        let p = Point::Specific { slot: 42, hash };
        assert_eq!(format!("{p}"), "42/abababababababab");
    }

    #[test]
    fn tip_round_trip() {
        let tip = Tip {
            point: Point::Specific {
                slot: 999,
                hash: [0x01; 32],
            },
            block_no: 500,
        };
        let encoded = minicbor::to_vec(&tip).unwrap();
        let decoded: Tip = minicbor::decode(&encoded).unwrap();
        assert_eq!(decoded, tip);
    }

    #[test]
    fn tip_origin_round_trip() {
        let tip = Tip {
            point: Point::Origin,
            block_no: 0,
        };
        let encoded = minicbor::to_vec(&tip).unwrap();
        let decoded: Tip = minicbor::decode(&encoded).unwrap();
        assert_eq!(decoded, tip);
    }

    #[test]
    fn decode_points_definite() {
        let p1 = Point::Origin;
        let p2 = Point::Specific {
            slot: 10,
            hash: [0xff; 32],
        };
        let mut buf = Vec::new();
        let mut e = minicbor::Encoder::new(&mut buf);
        encode_points(&mut e, &[p1.clone(), p2.clone()]).unwrap();

        let mut d = minicbor::Decoder::new(&buf);
        let points = decode_points(&mut d).unwrap();
        assert_eq!(points, vec![p1, p2]);
    }

    #[test]
    fn decode_points_indefinite() {
        // Build an indefinite-length array of one origin point.
        let buf = vec![
            0x9f, // begin indefinite array
            0x80, // origin point (empty definite array)
            0xff, // break
        ];

        let mut d = minicbor::Decoder::new(&buf);
        let points = decode_points(&mut d).unwrap();
        assert_eq!(points, vec![Point::Origin]);
    }

    #[test]
    fn decode_points_oversized_rejected() {
        // Craft an array claiming MAX_POINTS + 1 elements.
        let mut buf = Vec::new();
        let mut e = minicbor::Encoder::new(&mut buf);
        e.array((MAX_POINTS + 1) as u64).unwrap();
        // Don't need to write actual points — length check happens first.

        let mut d = minicbor::Decoder::new(&buf);
        let result = decode_points(&mut d);
        assert!(result.is_err());
    }
}
