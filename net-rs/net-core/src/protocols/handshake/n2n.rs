//! Node-to-Node handshake version data.
//!
//! The N2N version data is a CBOR array of 4 elements (for v11+):
//!   [networkMagic, diffusionMode, peerSharing, query]

use std::collections::BTreeMap;

use super::VersionTable;

/// N2N protocol version numbers currently supported.
pub const VERSION_V14: u64 = 14;
pub const VERSION_V15: u64 = 15;

/// Well-known network magic values.
pub const MAINNET_MAGIC: u64 = 764824073;
pub const TESTNET_MAGIC: u64 = 1097911063;
pub const PREVIEW_MAGIC: u64 = 2;
pub const PREPROD_MAGIC: u64 = 1;

/// Parsed N2N version data.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VersionData {
    pub network_magic: u64,
    /// True = initiator-only mode, False = initiator-and-responder.
    pub initiator_only_diffusion_mode: bool,
    /// 0 or 1: whether this node will run the PeerSharing protocol.
    pub peer_sharing: u8,
    /// True = query mode (send all supported versions and terminate).
    pub query: bool,
}

impl VersionData {
    /// Encode to CBOR bytes (for inclusion in the version table).
    pub fn encode(&self) -> Vec<u8> {
        minicbor::to_vec(self).expect("VersionData encoding cannot fail")
    }

    /// Decode from CBOR bytes.
    pub fn decode(bytes: &[u8]) -> Result<Self, String> {
        minicbor::decode(bytes).map_err(|e| format!("failed to decode N2N version data: {e}"))
    }
}

impl minicbor::Encode<()> for VersionData {
    fn encode<W: minicbor::encode::Write>(
        &self,
        e: &mut minicbor::Encoder<W>,
        _ctx: &mut (),
    ) -> Result<(), minicbor::encode::Error<W::Error>> {
        e.array(4)?;
        e.u64(self.network_magic)?;
        e.bool(self.initiator_only_diffusion_mode)?;
        e.u8(self.peer_sharing)?;
        e.bool(self.query)?;
        Ok(())
    }
}

impl<'a> minicbor::Decode<'a, ()> for VersionData {
    fn decode(
        d: &mut minicbor::Decoder<'a>,
        _ctx: &mut (),
    ) -> Result<Self, minicbor::decode::Error> {
        let len = d.array()?.ok_or_else(|| {
            minicbor::decode::Error::message("expected definite-length array for version data")
        })?;

        let network_magic = d.u64()?;
        let initiator_only_diffusion_mode = d.bool()?;

        // v7-v10 only have 2 fields; v11+ have 4.
        let (peer_sharing, query) = if len >= 4 {
            (d.u8()?, d.bool()?)
        } else {
            (0, false)
        };

        Ok(Self {
            network_magic,
            initiator_only_diffusion_mode,
            peer_sharing,
            query,
        })
    }
}

/// Build a version table proposing V14 and V15 with the given parameters.
pub fn version_table(data: &VersionData) -> VersionTable {
    let encoded = data.encode();
    let mut table = BTreeMap::new();
    table.insert(VERSION_V14, encoded.clone());
    table.insert(VERSION_V15, encoded);
    table
}

/// Standard N2N negotiation: find the highest common version, decode params,
/// check network magic matches. Returns the accepted version and negotiated
/// params, or a refuse reason.
pub fn negotiate(
    client_versions: &VersionTable,
    server_magic: u64,
) -> Result<(u64, Vec<u8>), super::RefuseReason> {
    // Our supported versions.
    let our_versions: Vec<u64> = vec![VERSION_V14, VERSION_V15];

    // Find highest common version.
    let common: Vec<u64> = our_versions
        .iter()
        .copied()
        .filter(|v| client_versions.contains_key(v))
        .collect();

    if common.is_empty() {
        return Err(super::RefuseReason::VersionMismatch(our_versions));
    }

    let best_version = *common.last().unwrap(); // safe: common is non-empty

    // Decode the client's params for the selected version.
    let client_params_bytes = &client_versions[&best_version];
    let client_data = VersionData::decode(client_params_bytes)
        .map_err(|e| super::RefuseReason::HandshakeDecodeError(best_version, e))?;

    // Check network magic.
    if client_data.network_magic != server_magic {
        return Err(super::RefuseReason::Refused(
            best_version,
            format!(
                "network magic mismatch: client={}, server={}",
                client_data.network_magic, server_magic
            ),
        ));
    }

    // Build negotiated version data per spec:
    // - diffusion mode = initiator-only if EITHER side proposes it (OR)
    // - peer sharing = inherited from remote
    // - query = inherited from client
    let negotiated = VersionData {
        network_magic: server_magic,
        initiator_only_diffusion_mode: client_data.initiator_only_diffusion_mode,
        peer_sharing: client_data.peer_sharing,
        query: client_data.query,
    };

    Ok((best_version, negotiated.encode()))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn version_data_round_trip() {
        let data = VersionData {
            network_magic: MAINNET_MAGIC,
            initiator_only_diffusion_mode: false,
            peer_sharing: 1,
            query: false,
        };
        let encoded = data.encode();
        let decoded = VersionData::decode(&encoded).unwrap();
        assert_eq!(data, decoded);
    }

    #[test]
    fn negotiate_success() {
        let client_data = VersionData {
            network_magic: MAINNET_MAGIC,
            initiator_only_diffusion_mode: false,
            peer_sharing: 0,
            query: false,
        };
        let client_table = version_table(&client_data);

        let (version, params) = negotiate(&client_table, MAINNET_MAGIC).unwrap();
        assert_eq!(version, VERSION_V15); // highest common
        let negotiated = VersionData::decode(&params).unwrap();
        assert_eq!(negotiated.network_magic, MAINNET_MAGIC);
    }

    #[test]
    fn negotiate_magic_mismatch() {
        let client_data = VersionData {
            network_magic: MAINNET_MAGIC,
            initiator_only_diffusion_mode: false,
            peer_sharing: 0,
            query: false,
        };
        let client_table = version_table(&client_data);

        let result = negotiate(&client_table, TESTNET_MAGIC);
        assert!(matches!(
            result,
            Err(super::super::RefuseReason::Refused(_, _))
        ));
    }

    #[test]
    fn negotiate_no_common_version() {
        let mut client_table = BTreeMap::new();
        let data = VersionData {
            network_magic: MAINNET_MAGIC,
            initiator_only_diffusion_mode: false,
            peer_sharing: 0,
            query: false,
        };
        client_table.insert(99, data.encode()); // unsupported version

        let result = negotiate(&client_table, MAINNET_MAGIC);
        assert!(matches!(
            result,
            Err(super::super::RefuseReason::VersionMismatch(_))
        ));
    }

    #[test]
    fn version_data_v7_v10_format_decode() {
        // v7-v10 used only 2 fields: [magic, diffusionMode].
        // Our decoder should handle this gracefully.
        let v10_cbor = minicbor::to_vec(&(MAINNET_MAGIC, false)).unwrap();
        let decoded = VersionData::decode(&v10_cbor).unwrap();
        assert_eq!(decoded.network_magic, MAINNET_MAGIC);
        assert!(!decoded.initiator_only_diffusion_mode);
        assert_eq!(decoded.peer_sharing, 0); // default
        assert!(!decoded.query); // default
    }

    #[test]
    fn version_data_all_fields_set() {
        let data = VersionData {
            network_magic: PREPROD_MAGIC,
            initiator_only_diffusion_mode: true,
            peer_sharing: 1,
            query: true,
        };
        let encoded = data.encode();
        let decoded = VersionData::decode(&encoded).unwrap();
        assert_eq!(decoded, data);
    }

    #[test]
    fn version_data_decode_from_live_bytes() {
        // The exact bytes the server returned for V15 params:
        // [764824073, false, 0, false]
        let live_bytes: &[u8] = &[0x84, 0x1a, 0x2d, 0x96, 0x4a, 0x09, 0xf4, 0x00, 0xf4];
        let decoded = VersionData::decode(live_bytes).unwrap();
        assert_eq!(decoded.network_magic, MAINNET_MAGIC);
        assert!(!decoded.initiator_only_diffusion_mode);
        assert_eq!(decoded.peer_sharing, 0);
        assert!(!decoded.query);
    }

    #[test]
    fn version_data_invalid_cbor() {
        let bad = &[0xFF, 0xFF];
        assert!(VersionData::decode(bad).is_err());
    }

    #[test]
    fn version_table_has_ascending_keys() {
        let data = VersionData {
            network_magic: MAINNET_MAGIC,
            initiator_only_diffusion_mode: false,
            peer_sharing: 0,
            query: false,
        };
        let table = version_table(&data);
        let keys: Vec<u64> = table.keys().copied().collect();
        assert_eq!(keys, vec![14, 15]); // ascending order
    }
}
