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

use minicbor::{Decoder, Encoder};
use minicbor::decode::Error as DecodeError;
use minicbor::encode::Error as EncodeError;

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
                let raw = d.input().get(start..end).ok_or_else(|| {
                    DecodeError::message("failed to extract version data bytes")
                })?;
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

fn decode_version_table(d: &mut Decoder<'_>) -> Result<VersionTable, DecodeError> {
    let len = d.map()?.ok_or_else(|| {
        DecodeError::message("expected definite-length map for version table")
    })?;

    let mut table = BTreeMap::new();
    for _ in 0..len {
        let version = d.u64()?;
        // Capture raw CBOR bytes for the version data value.
        let start = d.position();
        d.skip()?;
        let end = d.position();
        let raw = d.input().get(start..end).ok_or_else(|| {
            DecodeError::message("failed to extract version data bytes")
        })?;
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
}
