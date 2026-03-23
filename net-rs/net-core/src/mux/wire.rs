//! Ouroboros multiplexer wire format.
//!
//! Each segment on the wire has an 8-byte header followed by a payload:
//!
//! ```text
//!  0                   1                   2                   3
//!  0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1
//! +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
//! |                      Transmission Time                        |
//! +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
//! |M|     Mini Protocol ID        |        Payload Length n       |
//! +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
//! |                      Payload (n bytes)                        |
//! ```
//!
//! - Transmission Time: lower 32 bits of sender's monotonic clock (1 us resolution)
//! - M (Mode): 0 = initiator, 1 = responder
//! - Mini Protocol ID: 15-bit protocol number
//! - Payload Length: payload size in bytes (max 65535)

use std::io;

use byteorder::{BigEndian, ByteOrder};
use bytes::{Bytes, BytesMut};
use tokio::io::{AsyncRead, AsyncReadExt, AsyncWrite, AsyncWriteExt};

/// Wire header size in bytes.
pub const HEADER_LEN: usize = 8;

/// Maximum possible payload per the 16-bit length field.
pub const MAX_PAYLOAD_LEN: usize = 65535;

/// Parsed segment header.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Header {
    /// Transmission timestamp in microseconds (lower 32 bits of monotonic clock).
    pub timestamp: u32,
    /// Mode bit: 0 = initiator, 0x8000 = responder.
    pub mode: u16,
    /// Mini-protocol ID (0..32767).
    pub protocol: u16,
    /// Payload length in bytes.
    pub payload_len: u16,
}

impl Header {
    /// Encode the header into 8 bytes, big-endian.
    pub fn encode(&self, buf: &mut [u8; HEADER_LEN]) {
        BigEndian::write_u32(&mut buf[0..4], self.timestamp);
        BigEndian::write_u16(&mut buf[4..6], self.mode | self.protocol);
        BigEndian::write_u16(&mut buf[6..8], self.payload_len);
    }

    /// Decode a header from 8 bytes, big-endian.
    pub fn decode(buf: &[u8; HEADER_LEN]) -> Self {
        let timestamp = BigEndian::read_u32(&buf[0..4]);
        let protocol_field = BigEndian::read_u16(&buf[4..6]);
        let mode = protocol_field & 0x8000;
        let protocol = protocol_field & 0x7FFF;
        let payload_len = BigEndian::read_u16(&buf[6..8]);
        Self {
            timestamp,
            mode,
            protocol,
            payload_len,
        }
    }
}

/// A complete segment: header + payload.
#[derive(Debug, Clone)]
pub struct Segment {
    pub header: Header,
    pub payload: Bytes,
}

/// Read one complete segment from an async reader.
pub async fn read_segment<R: AsyncRead + Unpin>(reader: &mut R) -> io::Result<Segment> {
    let mut header_buf = [0u8; HEADER_LEN];
    reader.read_exact(&mut header_buf).await?;
    let header = Header::decode(&header_buf);

    let mut payload = BytesMut::zeroed(header.payload_len as usize);
    reader.read_exact(&mut payload).await?;

    Ok(Segment {
        header,
        payload: payload.freeze(),
    })
}

/// Write one complete segment to an async writer.
pub async fn write_segment<W: AsyncWrite + Unpin>(
    writer: &mut W,
    segment: &Segment,
) -> io::Result<()> {
    let mut header_buf = [0u8; HEADER_LEN];
    segment.header.encode(&mut header_buf);
    writer.write_all(&header_buf).await?;
    writer.write_all(&segment.payload).await?;
    writer.flush().await?;
    Ok(())
}

/// Split a payload into segments of at most `sdu_size` bytes.
pub fn segment_payload(
    protocol: u16,
    mode: u16,
    timestamp: u32,
    payload: &[u8],
    sdu_size: usize,
) -> Vec<Segment> {
    if payload.is_empty() {
        return vec![Segment {
            header: Header {
                timestamp,
                mode,
                protocol,
                payload_len: 0,
            },
            payload: Bytes::new(),
        }];
    }

    let sdu_size = sdu_size.min(MAX_PAYLOAD_LEN);
    payload
        .chunks(sdu_size)
        .map(|chunk| Segment {
            header: Header {
                timestamp,
                mode,
                protocol,
                payload_len: chunk.len() as u16,
            },
            payload: Bytes::copy_from_slice(chunk),
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn header_round_trip() {
        let header = Header {
            timestamp: 0x12345678,
            mode: 0x8000,
            protocol: 2,
            payload_len: 1024,
        };
        let mut buf = [0u8; HEADER_LEN];
        header.encode(&mut buf);
        let decoded = Header::decode(&buf);
        assert_eq!(header, decoded);
    }

    #[test]
    fn header_initiator_mode() {
        let header = Header {
            timestamp: 100,
            mode: 0,
            protocol: 3,
            payload_len: 42,
        };
        let mut buf = [0u8; HEADER_LEN];
        header.encode(&mut buf);
        let decoded = Header::decode(&buf);
        assert_eq!(decoded.mode, 0);
        assert_eq!(decoded.protocol, 3);
    }

    #[test]
    fn header_responder_mode() {
        let header = Header {
            timestamp: 100,
            mode: 0x8000,
            protocol: 4,
            payload_len: 0,
        };
        let mut buf = [0u8; HEADER_LEN];
        header.encode(&mut buf);
        // The wire byte at offset 4 should have bit 15 set
        let protocol_field = BigEndian::read_u16(&buf[4..6]);
        assert_eq!(protocol_field, 0x8004);
        let decoded = Header::decode(&buf);
        assert_eq!(decoded.mode, 0x8000);
        assert_eq!(decoded.protocol, 4);
    }

    #[test]
    fn header_max_protocol_id() {
        let header = Header {
            timestamp: 0,
            mode: 0,
            protocol: 0x7FFF,
            payload_len: 0,
        };
        let mut buf = [0u8; HEADER_LEN];
        header.encode(&mut buf);
        let decoded = Header::decode(&buf);
        assert_eq!(decoded.protocol, 0x7FFF);
    }

    #[test]
    fn segment_payload_splits_correctly() {
        let data = vec![0u8; 30000];
        let segments = segment_payload(2, 0, 0, &data, 12288);
        assert_eq!(segments.len(), 3); // 12288 + 12288 + 5424
        assert_eq!(segments[0].payload.len(), 12288);
        assert_eq!(segments[1].payload.len(), 12288);
        assert_eq!(segments[2].payload.len(), 5424);
        for seg in &segments {
            assert_eq!(seg.header.protocol, 2);
        }
    }

    #[test]
    fn segment_payload_empty() {
        let segments = segment_payload(0, 0, 0, &[], 12288);
        assert_eq!(segments.len(), 1);
        assert_eq!(segments[0].payload.len(), 0);
    }

    #[test]
    fn segment_payload_exact_sdu() {
        let data = vec![0u8; 12288];
        let segments = segment_payload(2, 0, 0, &data, 12288);
        assert_eq!(segments.len(), 1);
        assert_eq!(segments[0].payload.len(), 12288);
    }

    #[tokio::test]
    async fn read_write_segment_round_trip() {
        let segment = Segment {
            header: Header {
                timestamp: 42,
                mode: 0x8000,
                protocol: 2,
                payload_len: 5,
            },
            payload: Bytes::from_static(b"hello"),
        };

        let mut buf = Vec::new();
        write_segment(&mut buf, &segment).await.unwrap();
        assert_eq!(buf.len(), HEADER_LEN + 5);

        let mut cursor = &buf[..];
        let read_back = read_segment(&mut cursor).await.unwrap();
        assert_eq!(read_back.header, segment.header);
        assert_eq!(read_back.payload, segment.payload);
    }
}
