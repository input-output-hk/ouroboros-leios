# syntax=docker/dockerfile:1.7
#
# Build: from the repo root,
#   docker build -f net-rs/docker/Dockerfile -t piranha-relay .
#
# Build context must be the repo root because net-node depends on a
# sibling path crate at shared-rs/consensus.

FROM rust:1.92-slim-bookworm AS builder

RUN apt-get update && apt-get install -y --no-install-recommends \
        build-essential \
        pkg-config \
        ca-certificates \
    && rm -rf /var/lib/apt/lists/*

WORKDIR /build

# shared-rs is small, internal, and growing — copy the whole workspace
# rather than enumerate sub-crates, so adding a new shared-rs crate that
# net-node depends on doesn't silently break this build.
COPY shared-rs/ /build/shared-rs/

# net-rs: only the crates in net-node's dep closure. net-cli, net-cluster,
# net-ui, docs, scripts, logs, plans and the README are intentionally
# omitted to keep the build closure small in a fast-growing monorepo.
RUN mkdir -p /build/net-rs
COPY net-rs/Cargo.lock /build/net-rs/Cargo.lock
COPY net-rs/net-core/  /build/net-rs/net-core/
COPY net-rs/net-node/  /build/net-rs/net-node/

# Synthesise a minimal workspace Cargo.toml so cargo doesn't look for the
# omitted net-cli / net-cluster members. Lockfile entries for absent
# members are inert.
RUN printf '[workspace]\nmembers = ["net-core", "net-node"]\nresolver = "2"\n' \
    > /build/net-rs/Cargo.toml

WORKDIR /build/net-rs
RUN cargo build --release -p net-node


FROM debian:bookworm-slim AS runtime

RUN apt-get update && apt-get install -y --no-install-recommends \
        ca-certificates \
    && rm -rf /var/lib/apt/lists/*

RUN groupadd -r leios --gid 10001 \
    && useradd  -r -g leios --uid 10001 --home /home/leios --create-home leios

COPY --from=builder /build/net-rs/target/release/net-node /usr/local/bin/net-node
COPY net-rs/net-node/configs/mainnet.toml /etc/leios/mainnet.toml
COPY net-rs/docker/relay.toml             /etc/leios/relay.toml
COPY net-rs/docker/entrypoint.sh          /usr/local/bin/entrypoint.sh
RUN chmod +x /usr/local/bin/entrypoint.sh \
    && mkdir -p /run/net-node \
    && chown leios:leios /run/net-node

USER leios
WORKDIR /home/leios

ENV NET_NODE_LISTEN_PORT=3001 \
    RUST_LOG=info

EXPOSE 3001

ENTRYPOINT ["/usr/local/bin/entrypoint.sh"]
