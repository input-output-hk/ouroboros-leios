# Public Leios testnet relay image: ships the pinned configs alongside
# the patched cardano-node so the image runs as a non-block-producing
# relay against leios-node.play.dev.cardano.org out of the box.
#
# Build args:
#   BASE_IMAGE  cardano-node-leios base (statically-linked binaries).

ARG BASE_IMAGE=ghcr.io/input-output-hk/ouroboros-leios/cardano-node-leios:latest

FROM ${BASE_IMAGE} AS leios

FROM debian:bookworm-slim

COPY --from=leios /bin/cardano-node /usr/local/bin/cardano-node
COPY --from=leios /bin/cardano-cli  /usr/local/bin/cardano-cli

RUN apt-get update -y && \
    apt-get install -y --no-install-recommends \
      ca-certificates \
      jq && \
    rm -rf /var/lib/apt/lists/*

ENV WORKING_DIR=/data \
    SOURCE_DIR=/app \
    PORT=3010 \
    HOST_ADDR=0.0.0.0 \
    CARDANO_NODE=cardano-node \
    CARDANO_NODE_NETWORK_ID=164 \
    CARDANO_NODE_SOCKET_PATH=/data/node.socket

RUN mkdir -p ${WORKING_DIR} ${SOURCE_DIR}/config

# Pinned cardano-playground snapshot for the public Leios testnet:
# genesis files (byron/shelley/alonzo/conway/dijkstra), node config,
# topology, peer snapshot. Refresh with ./pin-config.sh.
COPY testnet/config/*.json ${SOURCE_DIR}/config/

# Just-the-node launcher. The orchestrator run.sh (process-compose +
# X-ray observability) is host-only; inside the container we run the
# node directly.
COPY testnet/run-node.sh ${SOURCE_DIR}/run-node.sh
RUN chmod +x ${SOURCE_DIR}/run-node.sh

EXPOSE 3010 12798

VOLUME ["/data"]

WORKDIR /data

CMD ["/app/run-node.sh"]
