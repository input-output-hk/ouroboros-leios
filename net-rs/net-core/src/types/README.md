# types — Shared Cardano Types

Core Cardano data types used across protocols: chain positions, headers, and blocks. All types include CBOR codecs for wire compatibility.

## Files

| File | Description |
|------|-------------|
| `mod.rs` | `Point`, `Tip`, and CBOR encode/decode helpers (`encode_points`, `decode_points`) |
| `header.rs` | `WrappedHeader` (raw CBOR + parsed info), `HeaderInfo` (Shelley+ header fields) |
| `block.rs` | `BlockBody` (raw CBOR + parsed info), `LeiosBlockInfo` (CIP-0164 EB certificate) |

## Types

| Type | Description |
|------|-------------|
| `Point` | Chain position: `Origin` or `Specific { slot: u64, hash: [u8; 32] }`. CBOR: origin = `[]`, specific = `[slot, hash]` |
| `Tip` | `Point` + `block_no: u64` — current chain tip position |
| `WrappedHeader` | Raw CBOR bytes (including `#6.24` tag wrapper) + optional parsed `HeaderInfo`. Byron headers return `None` gracefully |
| `HeaderInfo` | Parsed from Shelley+ header body array: `era`, `slot`, `block_number`, `prev_hash`, `issuer_vkey`, `body_size`, `block_body_hash`, plus CIP-0164 extensions (`announced_eb`, `certified_eb`) |
| `BlockBody` | Raw CBOR bytes + optional `LeiosBlockInfo`. MAX_BLOCK_SIZE: 2.5MB |
| `LeiosBlockInfo` | CIP-0164: extracted EB certificate bytes from block body (field 4 of Shelley+ block array, if present) |

## Header Parsing

`HeaderInfo` uses array-length disambiguation for optional Leios fields:
- 10 fields = base Shelley+ header
- 11 fields = base + `certified_eb`
- 12 fields = base + `announced_eb`
- 13 fields = base + both

Parsing is best-effort and silent — unknown formats return `None` rather than errors.

## Constants

- `MAX_POINTS`: 2048 — maximum points in a FindIntersect request
- `MAX_BLOCK_SIZE`: 2,500,000 bytes
