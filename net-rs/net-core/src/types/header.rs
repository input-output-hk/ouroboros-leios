//! Era-tagged block headers with optional parsed Shelley+ fields.

use minicbor::decode::Error as DecodeError;
use minicbor::encode::Error as EncodeError;
use minicbor::{Decoder, Encoder};

use super::{Point, MAX_HEADER_SIZE};

/// Number of base fields in a Shelley+ header_body array (before Leios extensions).
const HEADER_BODY_BASE_FIELDS: u64 = 10;

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

// --- Header hash ---

/// Compute Blake2b-256 hash of header CBOR bytes.
/// Used by both `WrappedHeader::point()` and `BlockBody::point()`.
pub(crate) fn header_hash(header_bytes: &[u8]) -> [u8; 32] {
    let result = blake2b_simd::Params::new()
        .hash_length(32)
        .hash(header_bytes);
    let mut hash = [0u8; 32];
    hash.copy_from_slice(result.as_bytes());
    hash
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

    /// Derive the chain Point (slot + header hash) from this header.
    ///
    /// Computes Blake2b-256 of the raw header CBOR for the block hash
    /// and combines with the parsed slot number.
    /// Returns None for Byron headers or unparseable data.
    pub fn point(&self) -> Option<Point> {
        let info = self.parsed.as_ref()?;
        let hash = header_hash(&self.raw);
        Some(Point::Specific {
            slot: info.slot,
            hash,
        })
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

#[cfg(test)]
mod tests {
    use super::*;
    use minicbor::Encoder;

    /// Build a fake Shelley+ header with the given fields for testing.
    /// Produces valid CBOR matching the wire format: [era_tag, #6.24(bytes .cbor [header_body, sig])]
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
        use minicbor::encode::Error as EncodeError;
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
    fn wrapped_header_point_returns_slot_and_hash() {
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
        let header = WrappedHeader::new(raw.clone());
        let point = header.point().expect("should derive point");
        match point {
            super::super::Point::Specific { slot, hash } => {
                assert_eq!(slot, 5000);
                // Hash should be blake2b-256 of the raw header bytes.
                let expected = header_hash(&raw);
                assert_eq!(hash, expected);
            }
            _ => panic!("expected Point::Specific"),
        }
    }

    #[test]
    fn wrapped_header_point_returns_none_for_opaque() {
        let header = WrappedHeader::opaque(vec![0xA0]);
        assert!(header.point().is_none());
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
}
