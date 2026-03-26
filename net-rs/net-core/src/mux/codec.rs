//! CBOR message framing over multiplexer channels.
//!
//! The Ouroboros multiplexer has no message-level framing — segments carry raw
//! bytes and multiple CBOR messages may span segments or be packed into one.
//! This module provides `CodecSend` and `CodecRecv` which handle CBOR
//! serialization/deserialization over the raw byte channels.

use bytes::{Bytes, BytesMut};

use super::channel::{ChannelRecv, ChannelSend};
use super::MuxError;

/// Sending half: CBOR-encodes messages and writes them to the channel.
pub struct CodecSend {
    channel: ChannelSend,
}

impl CodecSend {
    pub fn new(channel: ChannelSend) -> Self {
        Self { channel }
    }

    /// Encode a message to CBOR and send it through the mux channel.
    pub async fn send<T: minicbor::Encode<()>>(&self, msg: &T) -> Result<(), MuxError> {
        let encoded = minicbor::to_vec(msg).map_err(|e| {
            MuxError::Io(std::io::Error::new(
                std::io::ErrorKind::InvalidData,
                format!("CBOR encode error: {e}"),
            ))
        })?;
        self.channel.send(Bytes::from(encoded)).await
    }
}

/// Receiving half: reads bytes from the channel and incrementally CBOR-decodes
/// messages. Handles the case where a message spans multiple segments or
/// multiple messages arrive in a single segment.
///
/// Size limits are enforced at the demuxer level (via shared `IngressLimit`),
/// not here. The demuxer rejects oversized data at the segment level before
/// it reaches this buffer, allowing TCP backpressure to constrain the sender.
pub struct CodecRecv {
    channel: ChannelRecv,
    buffer: BytesMut,
}

impl CodecRecv {
    pub fn new(channel: ChannelRecv) -> Self {
        Self {
            channel,
            buffer: BytesMut::new(),
        }
    }

    /// Update the demuxer's ingress limit for this protocol channel.
    /// Called by the protocol runner when state changes, so the demuxer
    /// enforces per-state size limits at the segment level.
    pub fn set_ingress_limit(&self, limit: usize) {
        self.channel.set_ingress_limit(limit);
    }

    /// Receive and decode one CBOR message. Blocks until a complete message
    /// is available. Returns an error if the channel closes before a complete
    /// message is received.
    ///
    /// The decoded type must be owned (no borrows from the input buffer).
    /// This is necessary because the buffer is mutated between decode attempts.
    pub async fn recv<T: for<'a> minicbor::Decode<'a, ()>>(&mut self) -> Result<T, MuxError> {
        loop {
            // Try to decode a message from the buffer.
            if !self.buffer.is_empty() {
                match try_decode::<T>(&self.buffer) {
                    DecodeResult::Ok(value, consumed) => {
                        // Advance past the consumed bytes.
                        let _ = self.buffer.split_to(consumed);
                        return Ok(value);
                    }
                    DecodeResult::NeedMore => {
                        // Not enough data yet — fall through to read more.
                    }
                    DecodeResult::Error(e) => {
                        return Err(MuxError::Io(std::io::Error::new(
                            std::io::ErrorKind::InvalidData,
                            format!("CBOR decode error: {e}"),
                        )));
                    }
                }
            }

            // Read more data from the channel.
            match self.channel.recv().await {
                Some(chunk) => {
                    self.buffer.extend_from_slice(&chunk);
                }
                None => {
                    return Err(MuxError::Shutdown);
                }
            }
        }
    }
}

/// Result of attempting to decode a CBOR value from a byte buffer.
enum DecodeResult<T> {
    /// Successfully decoded a value, consuming `usize` bytes.
    Ok(T, usize),
    /// Not enough data in the buffer for a complete value.
    NeedMore,
    /// Unrecoverable decode error.
    Error(String),
}

/// Try to decode one CBOR value from the front of `data`.
fn try_decode<'a, T: minicbor::Decode<'a, ()>>(data: &'a [u8]) -> DecodeResult<T> {
    let mut decoder = minicbor::Decoder::new(data);
    match decoder.decode::<T>() {
        Ok(value) => {
            let consumed = decoder.position();
            DecodeResult::Ok(value, consumed)
        }
        Err(e) if e.is_end_of_input() => DecodeResult::NeedMore,
        Err(e) => DecodeResult::Error(e.to_string()),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bearer::mem::MemBearer;
    use crate::mux::scheduler::{RoundRobin, TrafficClass};
    use crate::mux::{Mux, MuxConfig, ProtocolConfig, MODE_INITIATOR, MODE_RESPONDER};

    /// Simple test type: a CBOR array [tag, payload].
    #[derive(Debug, PartialEq, Eq)]
    struct TestMsg {
        tag: u32,
        payload: Vec<u8>,
    }

    impl minicbor::Encode<()> for TestMsg {
        fn encode<W: minicbor::encode::Write>(
            &self,
            e: &mut minicbor::Encoder<W>,
            _ctx: &mut (),
        ) -> Result<(), minicbor::encode::Error<W::Error>> {
            e.array(2)?;
            e.u32(self.tag)?;
            e.bytes(&self.payload)?;
            Ok(())
        }
    }

    impl<'a> minicbor::Decode<'a, ()> for TestMsg {
        fn decode(
            d: &mut minicbor::Decoder<'a>,
            _ctx: &mut (),
        ) -> Result<Self, minicbor::decode::Error> {
            let _len = d.array()?;
            let tag = d.u32()?;
            let payload = d.bytes()?.to_vec();
            Ok(Self { tag, payload })
        }
    }

    fn test_mux_config() -> MuxConfig {
        MuxConfig {
            sdu_timeout: std::time::Duration::from_secs(2),
            ..MuxConfig::default()
        }
    }

    fn make_mux_pair(
        proto: &ProtocolConfig,
    ) -> (
        CodecSend,
        CodecRecv,
        crate::mux::RunningMux,
        crate::mux::RunningMux,
    ) {
        let (bearer_a, bearer_b) = MemBearer::pair();

        let mut mux_a = Mux::new(test_mux_config(), RoundRobin::default(), MODE_INITIATOR);
        let (send_ch, _recv_ch) = mux_a.register(proto);
        let running_a = mux_a.run(bearer_a);

        let mut mux_b = Mux::new(test_mux_config(), RoundRobin::default(), MODE_RESPONDER);
        let (_send_ch, recv_ch) = mux_b.register(proto);
        let running_b = mux_b.run(bearer_b);

        (
            CodecSend::new(send_ch),
            CodecRecv::new(recv_ch),
            running_a,
            running_b,
        )
    }

    #[tokio::test]
    async fn codec_round_trip() {
        let proto = ProtocolConfig {
            id: 0,
            traffic_class: TrafficClass::Priority,
            ingress_limit: 65535,
            egress_queue_size: 10,
        };
        let (codec_send, mut codec_recv, ra, rb) = make_mux_pair(&proto);

        let msg = TestMsg {
            tag: 42,
            payload: b"hello cbor".to_vec(),
        };
        codec_send.send(&msg).await.unwrap();

        let received: TestMsg = codec_recv.recv().await.unwrap();
        assert_eq!(received, msg);

        ra.abort();
        rb.abort();
    }

    #[tokio::test]
    async fn codec_multiple_messages() {
        let proto = ProtocolConfig {
            id: 0,
            traffic_class: TrafficClass::Priority,
            ingress_limit: 65535,
            egress_queue_size: 10,
        };
        let (codec_send, mut codec_recv, ra, rb) = make_mux_pair(&proto);

        for i in 0..3u32 {
            let msg = TestMsg {
                tag: i,
                payload: vec![i as u8; 10],
            };
            codec_send.send(&msg).await.unwrap();
        }

        for i in 0..3u32 {
            let received: TestMsg = codec_recv.recv().await.unwrap();
            assert_eq!(received.tag, i);
            assert_eq!(received.payload, vec![i as u8; 10]);
        }

        ra.abort();
        rb.abort();
    }

    #[tokio::test]
    async fn codec_large_message_spanning_segments() {
        // Send a message larger than the default SDU size (12288 bytes).
        // This forces the mux to split it across multiple segments.
        let proto = ProtocolConfig {
            id: 0,
            traffic_class: TrafficClass::Priority,
            ingress_limit: 100_000,
            egress_queue_size: 10,
        };
        let (codec_send, mut codec_recv, ra, rb) = make_mux_pair(&proto);

        let msg = TestMsg {
            tag: 1,
            payload: vec![0xAB; 30_000], // larger than 12KB SDU
        };
        codec_send.send(&msg).await.unwrap();

        let received: TestMsg = codec_recv.recv().await.unwrap();
        assert_eq!(received.tag, 1);
        assert_eq!(received.payload.len(), 30_000);
        assert!(received.payload.iter().all(|&b| b == 0xAB));

        ra.abort();
        rb.abort();
    }

    #[tokio::test]
    async fn ingress_limit_rejects_oversized_message() {
        // Set a small ingress limit — the demuxer should reject the message
        // at the segment level before it reaches the codec buffer.
        let proto = ProtocolConfig {
            id: 0,
            traffic_class: TrafficClass::Priority,
            ingress_limit: 100,
            egress_queue_size: 10,
        };
        let (bearer_a, bearer_b) = MemBearer::pair();

        let mut mux_a = Mux::new(test_mux_config(), RoundRobin::default(), MODE_INITIATOR);
        let (send_ch, _) = mux_a.register(&proto);
        let ra = mux_a.run(bearer_a);

        let mut mux_b = Mux::new(test_mux_config(), RoundRobin::default(), MODE_RESPONDER);
        let (_, recv_ch) = mux_b.register(&proto);
        let rb = mux_b.run(bearer_b);

        let codec_send = CodecSend::new(send_ch);
        let mut codec_recv = CodecRecv::new(recv_ch);

        // Send a message larger than the ingress limit.
        let msg = TestMsg {
            tag: 1,
            payload: vec![0xAB; 200],
        };
        codec_send.send(&msg).await.unwrap();

        // The recv should fail because the demuxer rejects the oversized data.
        let result: Result<TestMsg, _> = codec_recv.recv().await;
        assert!(result.is_err(), "should reject message exceeding ingress limit");

        ra.abort();
        rb.abort();
    }

    #[tokio::test]
    async fn codec_recv_returns_error_on_channel_close() {
        let proto = ProtocolConfig {
            id: 0,
            traffic_class: TrafficClass::Priority,
            ingress_limit: 65535,
            egress_queue_size: 10,
        };
        let (codec_send, mut codec_recv, ra, rb) = make_mux_pair(&proto);

        // Drop the sender side and abort the mux — the recv should fail.
        drop(codec_send);
        ra.abort();
        rb.abort();

        // Give tasks a moment to shut down.
        tokio::task::yield_now().await;

        let result: Result<TestMsg, _> = codec_recv.recv().await;
        assert!(result.is_err());
    }
}
