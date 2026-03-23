//! CBOR encoding for handshake messages.
//!
//! Wire format (from spec section 3.6.9):
//!
//!   msgProposeVersions = [0, versionTable]
//!   msgAcceptVersion   = [1, versionNumber, versionData]
//!   msgRefuse          = [2, refuseReason]
//!   msgQueryReply      = [3, versionTable]
//!
//!   versionTable = { * versionNumber => versionData }
//!
//!   refuseReasonVersionMismatch      = [0, [*versionNumbers]]
//!   refuseReasonHandshakeDecodeError = [1, versionNumber, tstr]
//!   refuseReasonRefused              = [2, versionNumber, tstr]

use std::collections::BTreeMap;

use minicbor::decode::Error as DecodeError;
use minicbor::encode::Error as EncodeError;
use minicbor::{Decoder, Encoder};

use super::{Message, RefuseReason, VersionTable};

// --- Encode ---

impl minicbor::Encode<()> for Message {
    fn encode<W: minicbor::encode::Write>(
        &self,
        e: &mut Encoder<W>,
        _ctx: &mut (),
    ) -> Result<(), EncodeError<W::Error>> {
        match self {
            Message::ProposeVersions(versions) => {
                e.array(2)?;
                e.u32(0)?;
                encode_version_table(e, versions)?;
            }
            Message::AcceptVersion(version, params) => {
                e.array(3)?;
                e.u32(1)?;
                e.u64(*version)?;
                // params is already CBOR-encoded version data — write it raw.
                e.writer_mut()
                    .write_all(params)
                    .map_err(EncodeError::write)?;
            }
            Message::Refuse(reason) => {
                e.array(2)?;
                e.u32(2)?;
                encode_refuse_reason(e, reason)?;
            }
            Message::QueryReply(versions) => {
                e.array(2)?;
                e.u32(3)?;
                encode_version_table(e, versions)?;
            }
        }
        Ok(())
    }
}

fn encode_version_table<W: minicbor::encode::Write>(
    e: &mut Encoder<W>,
    versions: &VersionTable,
) -> Result<(), EncodeError<W::Error>> {
    // Definite-length map, keys in ascending order (BTreeMap guarantees this).
    e.map(versions.len() as u64)?;
    for (version, params) in versions {
        e.u64(*version)?;
        // params is already CBOR-encoded — write raw.
        e.writer_mut()
            .write_all(params)
            .map_err(EncodeError::write)?;
    }
    Ok(())
}

fn encode_refuse_reason<W: minicbor::encode::Write>(
    e: &mut Encoder<W>,
    reason: &RefuseReason,
) -> Result<(), EncodeError<W::Error>> {
    match reason {
        RefuseReason::VersionMismatch(versions) => {
            e.array(2)?;
            e.u32(0)?;
            e.array(versions.len() as u64)?;
            for v in versions {
                e.u64(*v)?;
            }
        }
        RefuseReason::HandshakeDecodeError(version, msg) => {
            e.array(3)?;
            e.u32(1)?;
            e.u64(*version)?;
            e.str(msg)?;
        }
        RefuseReason::Refused(version, msg) => {
            e.array(3)?;
            e.u32(2)?;
            e.u64(*version)?;
            e.str(msg)?;
        }
    }
    Ok(())
}

// --- Decode ---

impl<'a> minicbor::Decode<'a, ()> for Message {
    fn decode(d: &mut Decoder<'a>, _ctx: &mut ()) -> Result<Self, DecodeError> {
        let _array_len = d.array()?;
        let tag = d.u32()?;

        match tag {
            0 => {
                let versions = decode_version_table(d)?;
                Ok(Message::ProposeVersions(versions))
            }
            1 => {
                let version = d.u64()?;
                // The remaining bytes in this array are the version data.
                // We need to capture them as raw CBOR. Use decoder position
                // to extract the raw bytes.
                let start = d.position();
                d.skip()?; // skip one CBOR value
                let end = d.position();
                let raw = d
                    .input()
                    .get(start..end)
                    .ok_or_else(|| DecodeError::message("failed to extract version data bytes"))?;
                Ok(Message::AcceptVersion(version, raw.to_vec()))
            }
            2 => {
                let reason = decode_refuse_reason(d)?;
                Ok(Message::Refuse(reason))
            }
            3 => {
                let versions = decode_version_table(d)?;
                Ok(Message::QueryReply(versions))
            }
            other => Err(DecodeError::message(format!(
                "unknown handshake message tag: {other}"
            ))),
        }
    }
}

/// Maximum number of versions in a version table. The handshake size limit
/// is 5760 bytes — even with minimal per-version overhead (~3 bytes key +
/// 1 byte value) you can't fit more than ~1000 entries.
const MAX_VERSION_TABLE_ENTRIES: u64 = 256;

/// Maximum number of version numbers in a VersionMismatch refuse reason.
const MAX_MISMATCH_VERSIONS: u64 = 256;

fn decode_version_table(d: &mut Decoder<'_>) -> Result<VersionTable, DecodeError> {
    let len = d
        .map()?
        .ok_or_else(|| DecodeError::message("expected definite-length map for version table"))?;

    if len > MAX_VERSION_TABLE_ENTRIES {
        return Err(DecodeError::message(format!(
            "version table has {len} entries, maximum is {MAX_VERSION_TABLE_ENTRIES}"
        )));
    }

    let mut table = BTreeMap::new();
    for _ in 0..len {
        let version = d.u64()?;
        // Capture raw CBOR bytes for the version data value.
        let start = d.position();
        d.skip()?;
        let end = d.position();
        let raw = d
            .input()
            .get(start..end)
            .ok_or_else(|| DecodeError::message("failed to extract version data bytes"))?;
        table.insert(version, raw.to_vec());
    }

    Ok(table)
}

fn decode_refuse_reason(d: &mut Decoder<'_>) -> Result<RefuseReason, DecodeError> {
    let _array_len = d.array()?;
    let tag = d.u32()?;

    match tag {
        0 => {
            let len = d.array()?.ok_or_else(|| {
                DecodeError::message("expected definite-length array for version mismatch")
            })?;
            if len > MAX_MISMATCH_VERSIONS {
                return Err(DecodeError::message(format!(
                    "version mismatch list has {len} entries, maximum is {MAX_MISMATCH_VERSIONS}"
                )));
            }
            let mut versions = Vec::with_capacity(len as usize);
            for _ in 0..len {
                versions.push(d.u64()?);
            }
            Ok(RefuseReason::VersionMismatch(versions))
        }
        1 => {
            let version = d.u64()?;
            let msg = d.str()?.to_string();
            Ok(RefuseReason::HandshakeDecodeError(version, msg))
        }
        2 => {
            let version = d.u64()?;
            let msg = d.str()?.to_string();
            Ok(RefuseReason::Refused(version, msg))
        }
        other => Err(DecodeError::message(format!(
            "unknown refuse reason tag: {other}"
        ))),
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
    fn propose_versions_round_trip() {
        let mut versions = BTreeMap::new();
        // Version 14 with some dummy params (CBOR-encoded [764824073, false, 0, false])
        let params_14 = minicbor::to_vec(&(764824073u64, false, 0u8, false)).unwrap();
        versions.insert(14, params_14.clone());
        versions.insert(15, params_14);

        let msg = Message::ProposeVersions(versions.clone());
        let decoded = round_trip(&msg);

        match decoded {
            Message::ProposeVersions(decoded_versions) => {
                assert_eq!(decoded_versions.len(), 2);
                assert!(decoded_versions.contains_key(&14));
                assert!(decoded_versions.contains_key(&15));
            }
            other => panic!("expected ProposeVersions, got {other:?}"),
        }
    }

    #[test]
    fn accept_version_round_trip() {
        let params = minicbor::to_vec(&(764824073u64, false, 0u8, false)).unwrap();
        let msg = Message::AcceptVersion(14, params.clone());
        let decoded = round_trip(&msg);

        match decoded {
            Message::AcceptVersion(v, p) => {
                assert_eq!(v, 14);
                assert_eq!(p, params);
            }
            other => panic!("expected AcceptVersion, got {other:?}"),
        }
    }

    #[test]
    fn refuse_version_mismatch_round_trip() {
        let msg = Message::Refuse(RefuseReason::VersionMismatch(vec![14, 15]));
        let decoded = round_trip(&msg);

        match decoded {
            Message::Refuse(RefuseReason::VersionMismatch(versions)) => {
                assert_eq!(versions, vec![14, 15]);
            }
            other => panic!("expected Refuse(VersionMismatch), got {other:?}"),
        }
    }

    #[test]
    fn refuse_decode_error_round_trip() {
        let msg = Message::Refuse(RefuseReason::HandshakeDecodeError(
            14,
            "bad params".to_string(),
        ));
        let decoded = round_trip(&msg);

        match decoded {
            Message::Refuse(RefuseReason::HandshakeDecodeError(v, s)) => {
                assert_eq!(v, 14);
                assert_eq!(s, "bad params");
            }
            other => panic!("expected Refuse(HandshakeDecodeError), got {other:?}"),
        }
    }

    #[test]
    fn query_reply_round_trip() {
        let mut versions = BTreeMap::new();
        versions.insert(14, vec![0x80]); // empty CBOR array
        let msg = Message::QueryReply(versions);
        let decoded = round_trip(&msg);

        match decoded {
            Message::QueryReply(v) => {
                assert_eq!(v.len(), 1);
                assert!(v.contains_key(&14));
            }
            other => panic!("expected QueryReply, got {other:?}"),
        }
    }

    // --- Test vectors captured from backbone.cardano.iog.io:3001 (2026-03-23) ---

    /// ProposeVersions payload: [0, {14: [764824073, false, 0, false], 15: [764824073, false, 0, false]}]
    const LIVE_PROPOSE_PAYLOAD: &[u8] = &[
        0x82, 0x00, 0xa2, 0x0e, 0x84, 0x1a, 0x2d, 0x96, 0x4a, 0x09, 0xf4, 0x00, 0xf4, 0x0f, 0x84,
        0x1a, 0x2d, 0x96, 0x4a, 0x09, 0xf4, 0x00, 0xf4,
    ];

    /// AcceptVersion payload: [1, 15, [764824073, false, 0, false]]
    const LIVE_ACCEPT_PAYLOAD: &[u8] = &[
        0x83, 0x01, 0x0f, 0x84, 0x1a, 0x2d, 0x96, 0x4a, 0x09, 0xf4, 0x00, 0xf4,
    ];

    #[test]
    fn decode_live_propose() {
        let msg: Message = minicbor::decode(LIVE_PROPOSE_PAYLOAD).unwrap();
        match msg {
            Message::ProposeVersions(versions) => {
                assert_eq!(versions.len(), 2);
                assert!(versions.contains_key(&14));
                assert!(versions.contains_key(&15));
                // Decode the version data for V14.
                let data: super::super::n2n::VersionData =
                    minicbor::decode(versions.get(&14).unwrap()).unwrap();
                assert_eq!(data.network_magic, 764824073);
                assert!(!data.initiator_only_diffusion_mode);
                assert_eq!(data.peer_sharing, 0);
                assert!(!data.query);
            }
            other => panic!("expected ProposeVersions, got {other:?}"),
        }
    }

    #[test]
    fn decode_live_accept() {
        let msg: Message = minicbor::decode(LIVE_ACCEPT_PAYLOAD).unwrap();
        match msg {
            Message::AcceptVersion(version, params) => {
                assert_eq!(version, 15);
                let data: super::super::n2n::VersionData = minicbor::decode(&params).unwrap();
                assert_eq!(data.network_magic, 764824073);
                assert!(!data.initiator_only_diffusion_mode);
                assert_eq!(data.peer_sharing, 0);
                assert!(!data.query);
            }
            other => panic!("expected AcceptVersion, got {other:?}"),
        }
    }

    #[test]
    fn encode_matches_live_propose() {
        // Build the same ProposeVersions our client sends.
        let data = super::super::n2n::VersionData {
            network_magic: 764824073,
            initiator_only_diffusion_mode: false,
            peer_sharing: 0,
            query: false,
        };
        let versions = super::super::n2n::version_table(&data);
        let msg = Message::ProposeVersions(versions);
        let encoded = minicbor::to_vec(&msg).unwrap();
        assert_eq!(
            encoded, LIVE_PROPOSE_PAYLOAD,
            "our encoding must match what the live node accepted"
        );
    }

    #[test]
    fn unknown_message_tag_fails() {
        // CBOR array [99] — unknown tag.
        let bad = &[0x82, 0x18, 0x63, 0x00];
        let result: Result<Message, _> = minicbor::decode(bad);
        assert!(result.is_err());
    }

    #[test]
    fn truncated_payload_fails() {
        // Take the first 5 bytes of a valid propose — incomplete.
        let truncated = &LIVE_PROPOSE_PAYLOAD[..5];
        let result: Result<Message, _> = minicbor::decode(truncated);
        assert!(result.is_err());
    }

    #[test]
    fn oversized_version_table_rejected() {
        // Craft a ProposeVersions with a map claiming 1000 entries.
        // Our limit is 256 — the length check rejects before iteration.
        let mut buf = Vec::new();
        let mut e = minicbor::Encoder::new(&mut buf);
        e.array(2).unwrap();
        e.u32(0).unwrap();
        e.map(1000).unwrap();
        let result: Result<Message, _> = minicbor::decode(&buf);
        assert!(result.is_err());
    }
}
