# Trace translator

The trace translator converts Leios node logs into traces in the format expected by the [Leios trace verifier](https://github.com/input-output-hk/ouroboros-leios/tree/main/leios-trace-verifier). For now, it only recognizes Praos events plus Linear Leios endorser block (EB) events; all other events are ignored.

## Example usage

The trace translator uses the standard input and the standard output to perform translations:

```bash
trace-translator.py < node.log > node-tv.json
```

Assuming that the input file `node.log` contains the following traces (each Leios node log line wraps the actual trace as a JSON-encoded string in its `message` field):

```json
{"level":"info","process":"Node0","replica":0,"message":"{\"at\":\"2026-06-19T21:03:04.100000000Z\",\"ns\":\"Forge.Loop.StartLeadershipCheck\",\"data\":{\"kind\":\"TraceStartLeadershipCheck\",\"slot\":0},\"sev\":\"Info\",\"thread\":\"45\",\"host\":\"node-0\"}"}
{"level":"info","process":"Node0","replica":0,"message":"{\"at\":\"2026-06-19T21:03:04.200000000Z\",\"ns\":\"Forge.Loop.AdoptedBlock\",\"data\":{\"blockHash\":\"26ab7db1ca55e69885665f625262118ef7db99172be6d3591ad2a8e9bfeabffa\",\"blockSize\":864,\"kind\":\"TraceAdoptedBlock\",\"slot\":0},\"sev\":\"Info\",\"thread\":\"34\",\"host\":\"node-0\"}"}
{"level":"info","process":"Node0","replica":0,"message":"{\"at\":\"2026-06-19T21:03:04.300000000Z\",\"ns\":\"BlockFetch.Client.CompletedBlockFetch\",\"data\":{\"block\":\"e996590b50ee39d640975de80b1c4ebfaa923866437d36b2d2ab08dacda2a09d\",\"kind\":\"CompletedBlockFetch\",\"peer\":{\"connectionId\":\"127.0.0.1:30001 127.0.0.1:30000\"},\"size\":2472},\"sev\":\"Info\",\"thread\":\"74\",\"host\":\"node-0\"}"}
{"level":"info","process":"Node0","replica":0,"message":"{\"at\":\"2026-06-19T21:03:05.000000000Z\",\"ns\":\"Consensus.LeiosKernel.TraceLeiosKernel\",\"data\":{\"closureSize\":6446,\"ebSize\":6446,\"hash\":\"f3c92edb54bf039e4144e3ff4620c57eb12242cdb225e505aad6d2fc1b743688\",\"kind\":\"LeiosBlockForged\",\"mempoolRestSize\":0,\"numTxs\":179,\"slot\":1},\"sev\":\"Debug\",\"thread\":\"58\",\"host\":\"node-0\"}"}
{"level":"info","process":"Node0","replica":0,"message":"{\"at\":\"2026-06-19T21:03:05.100000000Z\",\"ns\":\"LeiosFetch.Remote.Receive.Block\",\"data\":{\"kind\":\"Recv\",\"msg\":{\"ebBytesSize\":6446,\"ebHash\":\"f3c92edb54bf039e4144e3ff4620c57eb12242cdb225e505aad6d2fc1b743688\",\"kind\":\"MsgLeiosBlock\"},\"peer\":{\"connectionId\":\"127.0.0.1:30001 127.0.0.1:30000\"}},\"sev\":\"Info\",\"thread\":\"119\",\"host\":\"node-0\"}"}
{"level":"info","process":"Node0","replica":0,"message":"{\"at\":\"2026-06-19T21:03:06.000000000Z\",\"ns\":\"Forge.Loop.StartLeadershipCheck\",\"data\":{\"kind\":\"TraceStartLeadershipCheck\",\"slot\":1},\"sev\":\"Info\",\"thread\":\"45\",\"host\":\"node-0\"}"}
{"level":"info","process":"Node0","replica":0,"message":"{\"at\":\"2026-06-19T21:03:07.000000000Z\",\"ns\":\"Forge.Loop.StartLeadershipCheck\",\"data\":{\"kind\":\"TraceStartLeadershipCheck\",\"slot\":2},\"sev\":\"Info\",\"thread\":\"45\",\"host\":\"node-0\"}"}
```

Then the output file `node-tv.json` will contain the following resulting traces:

```json
{"message": {"type": "RBGenerated", "producer": "node-0", "slot": 0, "id": "26ab7db1ca55e69885665f625262118ef7db99172be6d3591ad2a8e9bfeabffa", "endorsement": null, "parent": null, "size": 864, "tx_payload_bytes": null}, "time_s": 0.1}
{"message": {"type": "RBReceived", "recipient": "node-0", "id": "e996590b50ee39d640975de80b1c4ebfaa923866437d36b2d2ab08dacda2a09d"}, "time_s": 0.1}
{"message": {"type": "EBGenerated", "id": "f3c92edb54bf039e4144e3ff4620c57eb12242cdb225e505aad6d2fc1b743688", "slot": 1, "pipeline": null, "producer": "node-0", "size_bytes": 6446, "input_blocks": null, "endorser_blocks": null}, "time_s": 0.7}
{"message": {"type": "EBReceived", "id": "f3c92edb54bf039e4144e3ff4620c57eb12242cdb225e505aad6d2fc1b743688", "slot": null, "pipeline": null, "producer": null, "sender": null, "recipient": "node-0"}, "time_s": 0.1}
{"message": {"type": "Slot", "node": "node-0", "slot": 0}, "time_s": 0.9}
{"message": {"type": "Slot", "node": "node-0", "slot": 1}, "time_s": 1.0}
```

## Input formats

The translator accepts trace lines in two shapes:

1. **Envelope-wrapped traces** — the format written to node log files (e.g. `tmp-devnet/nodeN/node.log`), where each line is `{"level":...,"process":...,"message":"<JSON-encoded trace>"}` (the format shown above). The translator unwraps the `message` field automatically and skips lines whose message is not a trace (such as the plain-text startup banner).
2. **Bare traces** — one trace object per line (the unwrapped trace), as emitted directly by the node tracer.

Timestamps with sub-microsecond (e.g. nanosecond) precision are accepted; fractional seconds are truncated to microseconds.

## Recognized events

The translator maps the following input event namespaces (`ns`) to output trace types; every other event is ignored.

| Input event (`ns`)                                            | Output type    |
| ------------------------------------------------------------- | -------------- |
| `Forge.Loop.StartLeadershipCheck`                             | `Slot`         |
| `Forge.Loop.AdoptedBlock`                                     | `RBGenerated`  |
| `BlockFetch.Client.CompletedBlockFetch`                       | `RBReceived`   |
| `Consensus.LeiosKernel.TraceLeiosKernel` (`LeiosBlockForged`) | `EBGenerated`  |
| `LeiosFetch.Remote.Receive.Block`                             | `EBReceived`   |

The first three are Praos events; the last two are Linear Leios EB events.

## Limitations

- The `parent` and `tx_payload_bytes` fields in `RBGenerated` traces are not available since these are not present in the input traces of type `Forge.Loop.AdoptedBlock`. A possible solution to the absence of the `parent` field may imply the use of the corresponding input trace of type `Forge.Loop.ForgedBlock`.
- The `slot`, `producer`, and `sender` fields in `EBReceived` traces are set to `null` because the `LeiosFetch.Remote.Receive.Block` event carries only the EB hash, not the originating slot or peer identities.
