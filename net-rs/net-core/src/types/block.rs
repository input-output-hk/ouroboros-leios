//! Raw block bodies with optional Leios metadata (CIP-0164).

use minicbor::decode::Error as DecodeError;
use minicbor::encode::Error as EncodeError;
use minicbor::{Decoder, Encoder};

use super::MAX_BLOCK_SIZE;

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
}
