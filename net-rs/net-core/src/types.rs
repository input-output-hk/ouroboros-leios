//! Shared Cardano types used across mini-protocols.
//!
//! Headers are parsed to extract common Shelley+ fields (slot, block number,
//! issuer, etc.) plus optional CIP-0164 Leios extensions. Block bodies remain
//! opaque — era-specific block decoding is out of scope for the network layer.

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

/// Number of base fields in a Shelley+ header_body array (before Leios extensions).
const HEADER_BODY_BASE_FIELDS: u64 = 10;

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

// --- HeaderInfo ---

/// Parsed fields from a Shelley+ block header.
///
/// Extracted from the header_body array inside the era-tagged, #6.24-wrapped
/// header CBOR. Fields we don't need at the network layer (VRF proofs,
/// operational cert, protocol version, body signature) are skipped.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct HeaderInfo {
    /// Era tag (2=Shelley, 3=Allegra, 4=Mary, 5=Alonzo, 6=Babbage, 7=Conway).
    pub era: u8,
    /// Block number.
    pub block_number: u64,
    /// Slot number.
    pub slot: u64,
    /// Hash of the previous block (None for genesis-successor).
    pub prev_hash: Option<[u8; 32]>,
    /// Issuer verification key hash (32 bytes).
    pub issuer_vkey: [u8; 32],
    /// Block body size in bytes.
    pub body_size: u32,
    /// Hash of the block body.
    pub block_body_hash: [u8; 32],
    /// CIP-0164 Leios: announced endorser block hash and byte size.
    pub announced_eb: Option<([u8; 32], u32)>,
    /// CIP-0164 Leios: whether this RB certifies the previous RB's EB.
    pub certified_eb: Option<bool>,
}

impl HeaderInfo {
    /// Try to parse Shelley+ header fields from raw WrappedHeader bytes.
    ///
    /// Returns None for Byron headers (era 0/1) or if parsing fails.
    /// Parsing failures are silent — this is best-effort extraction.
    ///
    /// Wire structure:
    /// ```text
    /// [era_tag, #6.24(bytes .cbor [header_body, body_signature])]
    /// ```
    pub fn parse(raw: &[u8]) -> Option<Self> {
        Self::try_parse(raw).ok()
    }

    fn try_parse(raw: &[u8]) -> Result<Self, DecodeError> {
        let mut d = Decoder::new(raw);

        // Outer: [era_tag, #6.24(bytes)]
        let _outer_len = d.array()?;
        let era = d.u32()? as u8;

        // Byron (era 0 or 1) has a different structure — skip it.
        if era < 2 {
            return Err(DecodeError::message("Byron header"));
        }

        // Unwrap #6.24 tag → get inner CBOR bytes.
        let tag = d.tag()?;
        if tag.as_u64() != 24 {
            return Err(DecodeError::message(format!(
                "expected CBOR tag 24, got {}",
                tag.as_u64()
            )));
        }
        let inner_bytes = d.bytes()?;

        // Inner: [header_body, body_signature]
        let mut inner = Decoder::new(inner_bytes);
        let _inner_len = inner.array()?;

        // header_body is itself an array
        let body_len = match inner.array()? {
            Some(n) => n,
            None => return Err(DecodeError::message("indefinite header_body")),
        };

        if body_len < HEADER_BODY_BASE_FIELDS {
            return Err(DecodeError::message(format!(
                "header_body has {body_len} fields, expected at least {HEADER_BODY_BASE_FIELDS}"
            )));
        }

        // Field 0: block_number
        let block_number = inner.u64()?;
        // Field 1: slot
        let slot = inner.u64()?;
        // Field 2: prev_hash (hash32 or null)
        let prev_hash = parse_optional_hash(&mut inner)?;
        // Field 3: issuer_vkey (bytes 32)
        let issuer_vkey = parse_hash32(&mut inner)?;
        // Field 4: vrf_vkey — skip
        inner.skip()?;
        // Field 5: vrf_result — skip
        inner.skip()?;
        // Field 6: body_size
        let body_size = inner.u32()?;
        // Field 7: block_body_hash
        let block_body_hash = parse_hash32(&mut inner)?;
        // Field 8: operational_cert — skip
        inner.skip()?;
        // Field 9: protocol_version — skip
        inner.skip()?;

        // CIP-0164 Leios extensions — optional trailing fields.
        // The array length alone determines which are present:
        //   10 = base only (no Leios)
        //   11 = +1 field: certified_eb (bool)
        //   12 = +2 fields: announced_eb (hash32 + uint32 pair)
        //   13 = +3 fields: announced_eb pair + certified_eb
        let extra = body_len - HEADER_BODY_BASE_FIELDS;

        let announced_eb = if extra >= 2 {
            let eb_hash = parse_hash32(&mut inner)?;
            let eb_size = inner.u32()?;
            Some((eb_hash, eb_size))
        } else {
            None
        };

        let certified_eb = if extra == 1 || extra == 3 {
            Some(inner.bool()?)
        } else {
            None
        };

        Ok(HeaderInfo {
            era,
            block_number,
            slot,
            prev_hash,
            issuer_vkey,
            body_size,
            block_body_hash,
            announced_eb,
            certified_eb,
        })
    }
}

/// Parse a 32-byte hash from the decoder.
fn parse_hash32(d: &mut Decoder<'_>) -> Result<[u8; 32], DecodeError> {
    let bytes = d.bytes()?;
    if bytes.len() != 32 {
        return Err(DecodeError::message(format!(
            "expected 32-byte hash, got {} bytes",
            bytes.len()
        )));
    }
    let mut hash = [0u8; 32];
    hash.copy_from_slice(bytes);
    Ok(hash)
}

/// Parse an optional hash: either a 32-byte bstr or null.
fn parse_optional_hash(d: &mut Decoder<'_>) -> Result<Option<[u8; 32]>, DecodeError> {
    let dt = d.datatype()?;
    if dt == minicbor::data::Type::Null {
        d.skip()?;
        return Ok(None);
    }
    parse_hash32(d).map(Some)
}

// --- WrappedHeader ---

/// An era-tagged block header stored as raw CBOR bytes, with optional parsed fields.
///
/// For Shelley+ headers, `parsed` contains extracted header fields including slot,
/// block number, issuer, and CIP-0164 Leios extensions. For Byron headers or
/// unparseable headers, `parsed` is None.
///
/// Wire format: raw bytes are passed through unchanged. The parsed fields are
/// derived from the raw bytes and not separately encoded.
#[derive(Debug, Clone)]
pub struct WrappedHeader {
    /// Raw CBOR bytes of the header (wire format).
    pub raw: Vec<u8>,
    /// Parsed header fields (Shelley+ only). None for Byron or parse failure.
    pub parsed: Option<HeaderInfo>,
}

impl WrappedHeader {
    /// Create a WrappedHeader from raw bytes, attempting to parse Shelley+ fields.
    pub fn new(raw: Vec<u8>) -> Self {
        let parsed = HeaderInfo::parse(&raw);
        Self { raw, parsed }
    }

    /// Create a WrappedHeader from raw bytes without parsing.
    /// Use for test fixtures with trivial CBOR that isn't a real header.
    pub fn opaque(raw: Vec<u8>) -> Self {
        Self { raw, parsed: None }
    }
}

impl PartialEq for WrappedHeader {
    fn eq(&self, other: &Self) -> bool {
        self.raw == other.raw
    }
}

impl Eq for WrappedHeader {}

impl minicbor::Encode<()> for WrappedHeader {
    fn encode<W: minicbor::encode::Write>(
        &self,
        e: &mut Encoder<W>,
        _ctx: &mut (),
    ) -> Result<(), EncodeError<W::Error>> {
        e.writer_mut()
            .write_all(&self.raw)
            .map_err(EncodeError::write)?;
        Ok(())
    }
}

impl<'a> minicbor::Decode<'a, ()> for WrappedHeader {
    fn decode(d: &mut Decoder<'a>, _ctx: &mut ()) -> Result<Self, DecodeError> {
        let start = d.position();
        d.skip()?;
        let end = d.position();
        let len = end - start;
        if len > MAX_HEADER_SIZE {
            return Err(DecodeError::message(format!(
                "header too large: {len} bytes exceeds limit {MAX_HEADER_SIZE}"
            )));
        }
        let raw = d
            .input()
            .get(start..end)
            .ok_or_else(|| DecodeError::message("failed to extract header bytes"))?;
        Ok(WrappedHeader::new(raw.to_vec()))
    }
}

// --- LeiosBlockInfo ---

/// Leios metadata parsed from a block body (CIP-0164).
///
/// The EB certificate is extracted from real blocks received via BlockFetch.
/// The Shelley+ block structure is:
///   `#6.24(bytes .cbor [era_tag, [header, tx_bodies, tx_witnesses, aux_data, ?eb_certificate]])`
/// Base field count = 4; a 5th element is the EB certificate.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct LeiosBlockInfo {
    /// Opaque EB certificate bytes, if present in this block.
    pub eb_certificate: Option<Vec<u8>>,
}

/// Number of base fields in a Shelley+ block array (before Leios extensions).
const BLOCK_BASE_FIELDS: u64 = 4;

impl LeiosBlockInfo {
    /// Try to parse Leios metadata from raw BlockBody bytes.
    ///
    /// Returns None for Byron blocks or blocks without an EB certificate.
    /// Parsing failures are silent — this is best-effort extraction.
    pub fn parse(raw: &[u8]) -> Option<Self> {
        Self::try_parse(raw).ok()
    }

    fn try_parse(raw: &[u8]) -> Result<Self, DecodeError> {
        let mut d = Decoder::new(raw);

        // Unwrap #6.24 tag
        let tag = d.tag()?;
        if tag.as_u64() != 24 {
            return Err(DecodeError::message(format!(
                "expected CBOR tag 24, got {}",
                tag.as_u64()
            )));
        }
        let inner_bytes = d.bytes()?;

        // Inner: [era_tag, era_block]
        let mut inner = Decoder::new(inner_bytes);
        let _outer_len = inner.array()?;
        let era = inner.u32()?;

        // Byron (era 0 or 1) — no Leios support
        if era < 2 {
            return Err(DecodeError::message("Byron block"));
        }

        // era_block: [header, tx_bodies, tx_witnesses, aux_data, ?eb_certificate]
        let block_len = match inner.array()? {
            Some(n) => n,
            None => return Err(DecodeError::message("indefinite block array")),
        };

        if block_len <= BLOCK_BASE_FIELDS {
            return Err(DecodeError::message("no Leios extension fields"));
        }

        // Skip base fields 0-3
        for _ in 0..BLOCK_BASE_FIELDS {
            inner.skip()?;
        }

        // Field 4: eb_certificate — extract as opaque bytes
        let cert_start = inner.position();
        inner.skip()?;
        let cert_end = inner.position();
        let cert_bytes = inner_bytes
            .get(cert_start..cert_end)
            .ok_or_else(|| DecodeError::message("failed to extract certificate bytes"))?;

        Ok(LeiosBlockInfo {
            eb_certificate: Some(cert_bytes.to_vec()),
        })
    }
}

// --- BlockBody ---

/// A full block stored as raw CBOR bytes (including the #6.24 tag wrapper),
/// with optional parsed Leios metadata.
///
/// For Shelley+ blocks with a CIP-0164 EB certificate, `leios` contains the
/// extracted certificate bytes. For blocks without one, `leios` is None.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BlockBody {
    /// Raw CBOR bytes of the block.
    pub raw: Vec<u8>,
    /// Parsed Leios metadata (Shelley+ only). None if no certificate or parse failure.
    pub leios: Option<LeiosBlockInfo>,
}

impl BlockBody {
    /// Create a BlockBody from raw bytes, attempting to parse Leios metadata.
    pub fn new(raw: Vec<u8>) -> Self {
        let leios = LeiosBlockInfo::parse(&raw);
        Self { raw, leios }
    }

    /// Create a BlockBody from raw bytes without parsing.
    /// Use for test fixtures with trivial CBOR that isn't a real block.
    pub fn opaque(raw: Vec<u8>) -> Self {
        Self { raw, leios: None }
    }
}

impl minicbor::Encode<()> for BlockBody {
    fn encode<W: minicbor::encode::Write>(
        &self,
        e: &mut Encoder<W>,
        _ctx: &mut (),
    ) -> Result<(), EncodeError<W::Error>> {
        e.writer_mut()
            .write_all(&self.raw)
            .map_err(EncodeError::write)?;
        Ok(())
    }
}

impl<'a> minicbor::Decode<'a, ()> for BlockBody {
    fn decode(d: &mut Decoder<'a>, _ctx: &mut ()) -> Result<Self, DecodeError> {
        let start = d.position();
        d.skip()?;
        let end = d.position();
        let len = end - start;
        if len > MAX_BLOCK_SIZE {
            return Err(DecodeError::message(format!(
                "block too large: {len} bytes exceeds limit {MAX_BLOCK_SIZE}"
            )));
        }
        let raw = d
            .input()
            .get(start..end)
            .ok_or_else(|| DecodeError::message("failed to extract block bytes"))?;
        Ok(BlockBody::new(raw.to_vec()))
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

// --- Test helpers ---

/// Build a fake Shelley+ header with the given fields for testing.
/// Produces valid CBOR matching the wire format: [era_tag, #6.24(bytes .cbor [header_body, sig])]
#[cfg(test)]
fn build_test_header(
    era: u8,
    block_number: u64,
    slot: u64,
    prev_hash: Option<[u8; 32]>,
    issuer_vkey: [u8; 32],
    body_size: u32,
    block_body_hash: [u8; 32],
    announced_eb: Option<([u8; 32], u32)>,
    certified_eb: Option<bool>,
) -> Vec<u8> {
    use std::io::Write as _;
    // Build header_body array
    let field_count = HEADER_BODY_BASE_FIELDS
        + if announced_eb.is_some() { 2 } else { 0 }
        + if certified_eb.is_some() { 1 } else { 0 };

    let mut body_buf = Vec::new();
    let mut be = Encoder::new(&mut body_buf);
    be.array(field_count).unwrap();
    be.u64(block_number).unwrap(); // 0
    be.u64(slot).unwrap(); // 1
    match prev_hash {
        // 2
        Some(h) => {
            be.bytes(&h).unwrap();
        }
        None => {
            be.null().unwrap();
        }
    }
    be.bytes(&issuer_vkey).unwrap(); // 3
    be.bytes(&[0u8; 32]).unwrap(); // 4: vrf_vkey (dummy)
    be.array(2).unwrap(); // 5: vrf_result (dummy)
    be.bytes(&[0u8; 32]).unwrap();
    be.bytes(&[0u8; 32]).unwrap();
    be.u32(body_size).unwrap(); // 6
    be.bytes(&block_body_hash).unwrap(); // 7
    be.array(4).unwrap(); // 8: operational_cert (dummy)
    be.bytes(&[0u8; 32]).unwrap();
    be.u64(0).unwrap();
    be.u64(0).unwrap();
    be.bytes(&[0u8; 64]).unwrap();
    be.array(2).unwrap(); // 9: protocol_version (dummy)
    be.u32(10).unwrap();
    be.u32(0).unwrap();

    if let Some((eb_hash, eb_size)) = announced_eb {
        be.bytes(&eb_hash).unwrap(); // 10
        be.u32(eb_size).unwrap(); // 11
    }
    if let Some(cert) = certified_eb {
        be.bool(cert).unwrap(); // 12 (or 10 if no EB)
    }

    // Build inner: [header_body, body_signature]
    let mut inner_buf = Vec::new();
    let mut ie = Encoder::new(&mut inner_buf);
    ie.array(2).unwrap();
    ie.writer_mut()
        .write_all(&body_buf)
        .map_err(|e| EncodeError::write(e))
        .unwrap();
    ie.bytes(&[0u8; 64]).unwrap(); // dummy signature

    // Build outer: [era_tag, #6.24(inner_bytes)]
    let mut outer_buf = Vec::new();
    let mut oe = Encoder::new(&mut outer_buf);
    oe.array(2).unwrap();
    oe.u32(era as u32).unwrap();
    oe.tag(minicbor::data::Tag::new(24)).unwrap();
    oe.bytes(&inner_buf).unwrap();

    outer_buf
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
    fn wrapped_header_round_trip() {
        // Use an era-tagged header stub: [6, #6.24(h'deadbeef')]
        let mut buf = Vec::new();
        let mut e = minicbor::Encoder::new(&mut buf);
        e.array(2).unwrap();
        e.u32(6).unwrap(); // Conway era tag
        e.tag(minicbor::data::Tag::new(24)).unwrap();
        e.bytes(&[0xde, 0xad, 0xbe, 0xef]).unwrap();

        let header = WrappedHeader::opaque(buf.clone());
        let encoded = minicbor::to_vec(&header).unwrap();
        assert_eq!(encoded, buf);

        let decoded: WrappedHeader = minicbor::decode(&encoded).unwrap();
        assert_eq!(decoded.raw, buf);
    }

    #[test]
    fn block_body_round_trip() {
        // Simulate #6.24(bytes): CBOR tag 24 wrapping some bytes.
        let mut buf = Vec::new();
        let mut e = minicbor::Encoder::new(&mut buf);
        e.tag(minicbor::data::Tag::new(24)).unwrap();
        e.bytes(&[0x01, 0x02, 0x03]).unwrap();

        let body = BlockBody::opaque(buf.clone());
        let encoded = minicbor::to_vec(&body).unwrap();
        assert_eq!(encoded, buf);

        let decoded: BlockBody = minicbor::decode(&encoded).unwrap();
        assert_eq!(decoded.raw, buf);
    }

    // --- HeaderInfo parser tests ---

    #[test]
    fn parse_conway_header_base_fields() {
        let raw = build_test_header(
            7,                // Conway
            12345,            // block_number
            67890,            // slot
            Some([0xAA; 32]), // prev_hash
            [0xBB; 32],       // issuer_vkey
            1024,             // body_size
            [0xCC; 32],       // block_body_hash
            None,             // no Leios EB
            None,             // no Leios certified_eb
        );

        let header = WrappedHeader::new(raw);
        let info = header.parsed.expect("should parse Conway header");
        assert_eq!(info.era, 7);
        assert_eq!(info.block_number, 12345);
        assert_eq!(info.slot, 67890);
        assert_eq!(info.prev_hash, Some([0xAA; 32]));
        assert_eq!(info.issuer_vkey, [0xBB; 32]);
        assert_eq!(info.body_size, 1024);
        assert_eq!(info.block_body_hash, [0xCC; 32]);
        assert_eq!(info.announced_eb, None);
        assert_eq!(info.certified_eb, None);
    }

    #[test]
    fn parse_header_with_announced_eb() {
        let eb_hash = [0xDD; 32];
        let raw = build_test_header(
            7,
            100,
            200,
            Some([0xAA; 32]),
            [0xBB; 32],
            2048,
            [0xCC; 32],
            Some((eb_hash, 65536)),
            None,
        );

        let info = HeaderInfo::parse(&raw).expect("should parse");
        assert_eq!(info.announced_eb, Some((eb_hash, 65536)));
        assert_eq!(info.certified_eb, None);
    }

    #[test]
    fn parse_header_with_certified_eb_only() {
        let raw = build_test_header(
            7,
            100,
            200,
            Some([0xAA; 32]),
            [0xBB; 32],
            2048,
            [0xCC; 32],
            None,
            Some(true),
        );

        let info = HeaderInfo::parse(&raw).expect("should parse");
        assert_eq!(info.announced_eb, None);
        assert_eq!(info.certified_eb, Some(true));
    }

    #[test]
    fn parse_header_with_both_leios_extensions() {
        let eb_hash = [0xEE; 32];
        let raw = build_test_header(
            7,
            100,
            200,
            Some([0xAA; 32]),
            [0xBB; 32],
            2048,
            [0xCC; 32],
            Some((eb_hash, 32768)),
            Some(false),
        );

        let info = HeaderInfo::parse(&raw).expect("should parse");
        assert_eq!(info.announced_eb, Some((eb_hash, 32768)));
        assert_eq!(info.certified_eb, Some(false));
    }

    #[test]
    fn parse_header_genesis_prev_hash() {
        let raw = build_test_header(2, 0, 0, None, [0x11; 32], 0, [0x22; 32], None, None);

        let info = HeaderInfo::parse(&raw).expect("should parse Shelley header");
        assert_eq!(info.era, 2);
        assert_eq!(info.prev_hash, None);
    }

    #[test]
    fn parse_byron_header_returns_none() {
        // Byron header: [0, [word32, #6.24(...)]]
        let mut buf = Vec::new();
        let mut e = Encoder::new(&mut buf);
        e.array(2).unwrap();
        e.u32(0).unwrap(); // Byron regular
        e.array(2).unwrap();
        e.u32(764824073).unwrap();
        e.tag(minicbor::data::Tag::new(24)).unwrap();
        e.bytes(&[0x80]).unwrap();

        assert!(HeaderInfo::parse(&buf).is_none());
    }

    #[test]
    fn parse_invalid_cbor_returns_none() {
        assert!(HeaderInfo::parse(&[0xFF]).is_none());
        assert!(HeaderInfo::parse(&[]).is_none());
    }

    #[test]
    fn parse_trivial_cbor_returns_none() {
        // Trivial CBOR used in test fixtures (e.g., [42])
        let buf = minicbor::to_vec(&[42u64]).unwrap();
        assert!(HeaderInfo::parse(&buf).is_none());
    }

    #[test]
    fn wrapped_header_new_parses_valid_header() {
        let raw = build_test_header(
            7,
            999,
            5000,
            Some([0xAA; 32]),
            [0xBB; 32],
            512,
            [0xCC; 32],
            None,
            None,
        );
        let header = WrappedHeader::new(raw);
        assert!(header.parsed.is_some());
        assert_eq!(header.parsed.as_ref().unwrap().slot, 5000);
    }

    #[test]
    fn wrapped_header_opaque_skips_parsing() {
        let raw = build_test_header(
            7,
            999,
            5000,
            Some([0xAA; 32]),
            [0xBB; 32],
            512,
            [0xCC; 32],
            None,
            None,
        );
        let header = WrappedHeader::opaque(raw);
        assert!(header.parsed.is_none());
    }

    #[test]
    fn wrapped_header_encode_decode_preserves_parsed() {
        let raw = build_test_header(
            7,
            42,
            100,
            Some([0xAA; 32]),
            [0xBB; 32],
            256,
            [0xCC; 32],
            Some(([0xDD; 32], 1024)),
            Some(true),
        );
        let header = WrappedHeader::new(raw);
        assert!(header.parsed.is_some());

        // Encode → decode should re-parse and get the same fields
        let encoded = minicbor::to_vec(&header).unwrap();
        let decoded: WrappedHeader = minicbor::decode(&encoded).unwrap();
        assert_eq!(decoded.parsed, header.parsed);
    }

    // --- LeiosBlockInfo parser tests ---

    /// Build a fake Shelley+ block body for testing.
    /// Produces: #6.24(bytes .cbor [era_tag, [header, txs, witnesses, aux, ?cert]])
    fn build_test_block(era: u8, eb_certificate: Option<&[u8]>) -> Vec<u8> {
        use std::io::Write as _;
        let field_count = BLOCK_BASE_FIELDS + if eb_certificate.is_some() { 1 } else { 0 };

        // Build inner block array: [header, txs, witnesses, aux, ?cert]
        let mut block_buf = Vec::new();
        let mut be = Encoder::new(&mut block_buf);
        be.array(field_count).unwrap();
        be.bytes(&[0x80]).unwrap(); // dummy header
        be.array(0).unwrap(); // empty tx_bodies
        be.array(0).unwrap(); // empty tx_witnesses
        be.null().unwrap(); // null auxiliary_data
        if let Some(cert) = eb_certificate {
            be.bytes(cert).unwrap();
        }

        // Build outer: [era_tag, block_array]
        let mut inner_buf = Vec::new();
        let mut ie = Encoder::new(&mut inner_buf);
        ie.array(2).unwrap();
        ie.u32(era as u32).unwrap();
        ie.writer_mut().write_all(&block_buf).unwrap();

        // Wrap in #6.24
        let mut outer_buf = Vec::new();
        let mut oe = Encoder::new(&mut outer_buf);
        oe.tag(minicbor::data::Tag::new(24)).unwrap();
        oe.bytes(&inner_buf).unwrap();

        outer_buf
    }

    #[test]
    fn parse_block_body_no_certificate() {
        let raw = build_test_block(7, None);
        assert!(LeiosBlockInfo::parse(&raw).is_none());
    }

    #[test]
    fn parse_block_body_with_certificate() {
        let cert_data = vec![0xCA, 0xFE, 0xBA, 0xBE];
        let raw = build_test_block(7, Some(&cert_data));
        let info = LeiosBlockInfo::parse(&raw).expect("should parse");
        let cert = info.eb_certificate.expect("should have certificate");
        // Certificate is stored as an opaque CBOR span (bytes item with header).
        // Verify the content is there by decoding the bstr.
        let mut d = Decoder::new(&cert);
        let decoded = d.bytes().unwrap();
        assert_eq!(decoded, &cert_data);
    }

    #[test]
    fn parse_block_body_byron_returns_none() {
        let raw = build_test_block(0, None);
        assert!(LeiosBlockInfo::parse(&raw).is_none());
    }

    #[test]
    fn parse_block_body_invalid_returns_none() {
        assert!(LeiosBlockInfo::parse(&[0xFF]).is_none());
        assert!(LeiosBlockInfo::parse(&[]).is_none());
    }

    #[test]
    fn block_body_new_parses_certificate() {
        let cert_data = vec![0x01, 0x02, 0x03];
        let raw = build_test_block(7, Some(&cert_data));
        let body = BlockBody::new(raw);
        assert!(body.leios.is_some());
        assert!(body.leios.unwrap().eb_certificate.is_some());
    }

    #[test]
    fn block_body_opaque_skips_parsing() {
        let raw = build_test_block(7, Some(&[0x01]));
        let body = BlockBody::opaque(raw);
        assert!(body.leios.is_none());
    }

    // --- Existing tests ---

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
        let mut buf = Vec::new();
        buf.push(0x9f); // begin indefinite array
        buf.push(0x80); // origin point (empty definite array)
        buf.push(0xff); // break

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
