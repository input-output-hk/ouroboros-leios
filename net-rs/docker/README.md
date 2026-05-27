# piranha-relay Docker image

Single-relay Docker image for `net-node`. Runs as a passive Leios participant: `stake = 0` and `tx_rate = 0.0`, so the node diffuses EBs, votes and EB-tx bodies for its peers without producing any blocks or transactions itself.

## Build

From the **repository root** (not from `net-rs/`):

```sh
docker build -f net-rs/docker/Dockerfile -t piranha-relay .
```

The build context must be the repo root because `net-node` depends on the sibling path crate at `shared-rs/consensus`. A per-Dockerfile `Dockerfile.dockerignore` next to the Dockerfile keeps the context to ~1.6 MB by allow-listing only `net-rs/` and `shared-rs/`. Requires BuildKit (signalled by `# syntax=docker/dockerfile:1.7` at the top of the Dockerfile); on Ubuntu, `sudo apt install docker-buildx` if `docker buildx version` reports the plugin missing.

Resulting image is ~95 MB (debian:bookworm-slim base + static-linked `net-node`).

## Run

The container reads its configuration from three TOML layers (left-to-right wins):

1. `/etc/leios/mainnet.toml` — baked-in mainnet parameters from `net-node/configs/`.
2. `/etc/leios/relay.toml` — passive-relay defaults (see `relay.toml` in this directory).
3. An overlay rendered at startup from environment variables.
4. *(optional)* `$NET_NODE_CONFIG` — user-supplied TOML, applied last.

### Environment variables

| Var | Default | Notes |
|---|---|---|
| `NET_NODE_LISTEN_PORT` | `3001` | Bind address is always `0.0.0.0:$PORT`. |
| `NET_NODE_PEERS` | *(none)* | CSV of `host:port` outbound peers. Rendered into `[[peers]]` array-of-tables. |
| `NET_NODE_ID` | *(none)* | Logical node identifier. Must match `[A-Za-z0-9._-]+`; the entrypoint exits 64 if it doesn't. |
| `NET_NODE_CONFIG` | *(none)* | Absolute path **inside the container** to a user TOML overlay. Must be readable; the entrypoint exits 64 if not. |
| `RUST_LOG` | `info` | Standard `tracing` filter syntax. |

### Examples

Standalone relay, two outbound peers:

```sh
docker run --rm \
  --name piranha-relay \
  -p 3001:3001 \
  -e NET_NODE_ID=relay-eu-1 \
  -e NET_NODE_PEERS="relay-a.example:3001,relay-b.example:3001" \
  piranha-relay
```

With a user TOML overlay (e.g. to override telemetry sinks or enable production):

```sh
docker run --rm \
  -p 3001:3001 \
  -v "$PWD/my-overrides.toml:/etc/leios/user.toml:ro" \
  -e NET_NODE_CONFIG=/etc/leios/user.toml \
  -e NET_NODE_ID=relay-eu-1 \
  -e NET_NODE_PEERS="relay-a.example:3001" \
  piranha-relay
```

Non-default port:

```sh
docker run --rm \
  -p 4001:4001 \
  -e NET_NODE_LISTEN_PORT=4001 \
  -e NET_NODE_PEERS="relay-a.example:3001" \
  piranha-relay
```

### Container details

- Runs as non-root user `leios` (uid/gid 10001).
- `EXPOSE 3001` — remap on the host with `-p` as needed.
- Entrypoint `exec`s `net-node` directly, so SIGTERM propagates and shutdown is clean.
- Overlay TOML is written to `/run/net-node/overlay.toml` at startup; that path is writable by the `leios` user. Mount user overlays read-only somewhere else (e.g. `/etc/leios/user.toml`) and point `NET_NODE_CONFIG` at it.

## Files in this directory

- `Dockerfile` — multi-stage build (`rust:1.92-slim-bookworm` builder onto `debian:bookworm-slim` runtime).
- `Dockerfile.dockerignore` — strict allow-list, scoped to this Dockerfile via BuildKit's per-Dockerfile ignore convention. Does **not** affect other builds in the monorepo.
- `entrypoint.sh` — env-var → overlay TOML renderer + `exec net-node`.
- `relay.toml` — passive-relay TOML layer (between `mainnet.toml` and the env overlay).
