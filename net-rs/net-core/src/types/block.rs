//! Raw block bodies with optional Leios metadata (CIP-0164).

use minicbor::decode::Error as DecodeError;
use minicbor::encode::Error as EncodeError;
use minicbor::{Decoder, Encoder};

use super::{Point, MAX_BLOCK_SIZE};

/// Number of base fields in a Shelley+ block array (before Leios extensions).
const BLOCK_BASE_FIELDS: u64 = 4;

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

    /// Derive the chain Point (slot + header hash) from this block's raw bytes.
    ///
    /// Extracts the header from the block, parses it for the slot number,
    /// and computes Blake2b-256 of the header CBOR for the block hash.
    /// Returns None for Byron blocks or unparseable data.
    pub fn point(&self) -> Option<Point> {
        self.try_point().ok()
    }

    /// Extract the header from this block body as a WrappedHeader.
    ///
    /// Returns None for Byron blocks or unparseable data.
    pub fn header(&self) -> Option<super::WrappedHeader> {
        let buf = self.try_extract_header().ok()?;
        Some(super::WrappedHeader::new(buf))
    }

    /// Extract the header from this block in ChainSync wire format:
    /// `[era_tag, #6.24(header_cbor)]`.
    ///
    /// Inside the block, the header is stored as raw CBOR `[header_body, sig]`.
    /// This method wraps it in `#6.24` to match the ChainSync wire format,
    /// ensuring consistent hashing and downstream compatibility.
    fn try_extract_header(&self) -> Result<Vec<u8>, DecodeError> {
        let mut d = Decoder::new(&self.raw);

        // Unwrap #6.24 tag
        let tag = d.tag()?;
        if tag.as_u64() != 24 {
            return Err(DecodeError::message("expected CBOR tag 24"));
        }
        let inner_bytes = d.bytes()?;

        // Inner: [era_tag, era_block]
        let mut inner = Decoder::new(inner_bytes);
        let _outer_len = inner.array()?;
        let era = inner.u32()?;

        if era < 2 {
            return Err(DecodeError::message("Byron block"));
        }

        // era_block: [header, tx_bodies, ...]
        // Record position before/after header to extract its raw bytes.
        let _block_len = inner.array()?;
        let header_start = inner.position();
        inner.skip()?; // skip header
        let header_end = inner.position();

        let header_inner_bytes = inner_bytes
            .get(header_start..header_end)
            .ok_or_else(|| DecodeError::message("failed to extract header bytes"))?;

        // Reconstruct in ChainSync wire format: [era_tag, #6.24(header_cbor)]
        let mut header_buf = Vec::new();
        let mut he = Encoder::new(&mut header_buf);
        he.array(2)
            .map_err(|_| DecodeError::message("encode error"))?;
        he.u32(era)
            .map_err(|_| DecodeError::message("encode error"))?;
        he.tag(minicbor::data::Tag::new(24))
            .map_err(|_| DecodeError::message("encode error"))?;
        he.bytes(header_inner_bytes)
            .map_err(|_| DecodeError::message("encode error"))?;

        Ok(header_buf)
    }

    fn try_point(&self) -> Result<Point, DecodeError> {
        let header_buf = self.try_extract_header()?;

        // Parse header for slot.
        let info = super::HeaderInfo::parse(&header_buf)
            .ok_or_else(|| DecodeError::message("failed to parse header"))?;

        // Compute Blake2b-256 of the full header CBOR for the block hash.
        let hash = super::header::header_hash(&header_buf);

        Ok(Point::Specific {
            slot: info.slot,
            hash,
        })
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

#[cfg(test)]
mod tests {
    use super::*;
    use minicbor::Encoder;

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

    /// Build a block with a real parseable Shelley+ header for point() testing.
    fn build_block_with_header(era: u8, slot: u64) -> Vec<u8> {
        use std::io::Write as _;

        // Build header_body: [block_number, slot, prev_hash, issuer_vkey,
        //   vrf_vkey, vrf_result, body_size, block_body_hash, op_cert, proto_ver]
        let mut hb_buf = Vec::new();
        let mut hb = Encoder::new(&mut hb_buf);
        hb.array(10).unwrap();
        hb.u64(42).unwrap(); // block_number
        hb.u64(slot).unwrap(); // slot
        hb.bytes(&[0xAA; 32]).unwrap(); // prev_hash
        hb.bytes(&[0xBB; 32]).unwrap(); // issuer_vkey
        hb.bytes(&[0u8; 32]).unwrap(); // vrf_vkey
        hb.array(2).unwrap(); // vrf_result
        hb.bytes(&[0u8; 32]).unwrap();
        hb.bytes(&[0u8; 32]).unwrap();
        hb.u32(1024).unwrap(); // body_size
        hb.bytes(&[0xCC; 32]).unwrap(); // block_body_hash
        hb.array(4).unwrap(); // op_cert
        hb.bytes(&[0u8; 32]).unwrap();
        hb.u64(0).unwrap();
        hb.u64(0).unwrap();
        hb.bytes(&[0u8; 64]).unwrap();
        hb.array(2).unwrap(); // proto_ver
        hb.u32(10).unwrap();
        hb.u32(0).unwrap();

        // Build header: [header_body, body_signature]
        let mut header_buf = Vec::new();
        let mut hi = Encoder::new(&mut header_buf);
        hi.array(2).unwrap();
        hi.writer_mut().write_all(&hb_buf).unwrap();
        hi.bytes(&[0u8; 64]).unwrap(); // dummy signature

        // Block array: [header, txs, witnesses, aux]
        // Note: real Cardano blocks store the header directly (no #6.24 wrapping).
        let mut block_buf = Vec::new();
        let mut be = Encoder::new(&mut block_buf);
        be.array(4).unwrap();
        be.writer_mut().write_all(&header_buf).unwrap();
        be.array(0).unwrap(); // txs
        be.array(0).unwrap(); // witnesses
        be.null().unwrap(); // aux

        // Outer: [era_tag, block_array]
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
    fn block_body_point_extracts_slot_and_hash() {
        let raw = build_block_with_header(7, 67890);
        let body = BlockBody::new(raw);
        let point = body
            .point()
            .expect("should derive point from Shelley+ block");
        match point {
            Point::Specific { slot, hash } => {
                assert_eq!(slot, 67890);
                // Hash should be Blake2b-256 of the reconstructed header CBOR.
                // Just verify it's nonzero (deterministic but hard to precompute).
                assert_ne!(hash, [0u8; 32]);
            }
            Point::Origin => panic!("expected Specific point"),
        }
    }

    #[test]
    fn block_body_header_extracts_matching_point() {
        let raw = build_block_with_header(7, 99999);
        let body = BlockBody::new(raw);
        let header = body.header().expect("should extract header");
        let body_point = body.point().expect("should derive point");
        let header_point = header.point().expect("header should have point");
        assert_eq!(body_point, header_point);
    }

    #[test]
    fn block_body_header_byron_returns_none() {
        let raw = build_test_block(0, None);
        let body = BlockBody::new(raw);
        assert!(body.header().is_none());
    }

    #[test]
    fn block_body_point_byron_returns_none() {
        let raw = build_test_block(0, None);
        let body = BlockBody::new(raw);
        assert!(body.point().is_none());
    }

    #[test]
    fn block_body_point_invalid_returns_none() {
        let body = BlockBody::opaque(vec![0xFF]);
        assert!(body.point().is_none());
    }
}
