/// Capture raw handshake bytes from a live Cardano node for test vectors.

use std::net::ToSocketAddrs;

use tokio::io::{AsyncReadExt, AsyncWriteExt};
use tokio::net::TcpStream;

use net_core::mux::wire::{Header, HEADER_LEN};
use net_core::protocols::handshake::n2n;

pub async fn run(host: &str, magic: u64) -> Result<(), Box<dyn std::error::Error>> {
    let addr = host
        .to_socket_addrs()?
        .next()
        .ok_or_else(|| format!("could not resolve {host}"))?;

    println!("connecting to {addr}...");
    let mut stream = TcpStream::connect(addr).await?;
    stream.set_nodelay(true)?;

    // Build the handshake propose message manually through our codec.
    let versions = n2n::version_table(&n2n::VersionData {
        network_magic: magic,
        initiator_only_diffusion_mode: false,
        peer_sharing: 0,
        query: false,
    });
    let msg = net_core::protocols::handshake::Message::ProposeVersions(versions);
    let cbor_payload = minicbor::to_vec(&msg).unwrap();

    // Build the mux segment manually.
    let header = Header {
        timestamp: 0,
        mode: 0, // initiator
        protocol: 0, // handshake
        payload_len: cbor_payload.len() as u16,
    };
    let mut header_bytes = [0u8; HEADER_LEN];
    header.encode(&mut header_bytes);

    // Send and capture what we sent.
    let mut sent = Vec::new();
    sent.extend_from_slice(&header_bytes);
    sent.extend_from_slice(&cbor_payload);

    println!("sending {} bytes (header {} + payload {})", sent.len(), HEADER_LEN, cbor_payload.len());
    println!("sent hex: {}", hex(&sent));

    stream.write_all(&sent).await?;
    stream.flush().await?;

    // Read the response segment.
    let mut resp_header = [0u8; HEADER_LEN];
    stream.read_exact(&mut resp_header).await?;
    let resp_hdr = Header::decode(&resp_header);
    println!(
        "response header: protocol={}, mode=0x{:04x}, payload_len={}",
        resp_hdr.protocol, resp_hdr.mode, resp_hdr.payload_len
    );

    let mut resp_payload = vec![0u8; resp_hdr.payload_len as usize];
    stream.read_exact(&mut resp_payload).await?;

    let mut received = Vec::new();
    received.extend_from_slice(&resp_header);
    received.extend_from_slice(&resp_payload);

    println!("received {} bytes total", received.len());
    println!("received hex: {}", hex(&received));

    // Try to decode the response.
    let resp_msg: net_core::protocols::handshake::Message =
        minicbor::decode(&resp_payload).map_err(|e| format!("decode error: {e}"))?;
    println!("decoded: {resp_msg:?}");

    // Print as Rust byte array literals for test vectors.
    println!("\n// Test vector: client -> server (ProposeVersions)");
    println!("const PROPOSE_SEGMENT: &[u8] = &{};", rust_bytes(&sent));
    println!("const PROPOSE_PAYLOAD: &[u8] = &{};", rust_bytes(&cbor_payload));

    println!("\n// Test vector: server -> client (AcceptVersion or Refuse)");
    println!("const RESPONSE_SEGMENT: &[u8] = &{};", rust_bytes(&received));
    println!("const RESPONSE_PAYLOAD: &[u8] = &{};", rust_bytes(&resp_payload));

    Ok(())
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect::<Vec<_>>().join("")
}

fn rust_bytes(bytes: &[u8]) -> String {
    let items: Vec<String> = bytes.iter().map(|b| format!("0x{b:02x}")).collect();
    format!("[{}]", items.join(", "))
}
