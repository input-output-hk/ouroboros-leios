# protocols — Cardano Mini-Protocols

Eight mini-protocols implementing the Cardano N2N network stack: six Praos protocols plus two Leios (CIP-0164) extensions. Each protocol is a state machine with CBOR-encoded messages, agency rules, size limits, and timeouts.

## Protocol Framework

The `Protocol` trait and `Runner` (in `protocol.rs`) provide agency-checked state machine execution:

```rust
trait Protocol {
    type State;    // state machine states
    type Message;  // CBOR-encodable messages

    fn initial_state() -> Self::State;
    fn agency(state: &Self::State) -> Agency;  // Client | Server | Nobody
    fn transition(state: &Self::State, msg: &Self::Message) -> Result<Self::State>;
    fn size_limit(state: &Self::State) -> usize;
    fn timeout(state: &Self::State) -> Option<Duration>;
}
```

`Runner<P>` wraps codec + state, enforcing that only the party with agency can send. Protocols use `runner.send(msg)` and `runner.recv()` directly in async functions.

## Protocols

| Protocol | ID | Priority | Description | README |
|----------|----|----------|-------------|--------|
| Handshake | 0 | 0 | Version negotiation | [handshake/](handshake/) |
| ChainSync | 2 | 1 | Chain tip tracking, intersection finding | [chainsync/](chainsync/) |
| BlockFetch | 3 | 2 | Block range retrieval | [blockfetch/](blockfetch/) |
| TxSubmission | 4 | 3 | Pull-based transaction dissemination | [txsubmission/](txsubmission/) |
| KeepAlive | 8 | 4 | Ping/pong liveness and RTT | [keepalive/](keepalive/) |
| PeerSharing | 10 | 7 | Peer discovery | [peersharing/](peersharing/) |
| LeiosNotify | 18 | 6 | Leios data announcements (CIP-0164) | [leios_notify/](leios_notify/) |
| LeiosFetch | 19 | 5 | Leios data retrieval (CIP-0164) | [leios_fetch/](leios_fetch/) |
