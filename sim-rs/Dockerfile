FROM rust:1.82-slim AS builder

WORKDIR /usr/src/sim-rs
COPY sim-rs/ .

RUN cargo build --release

FROM debian:bookworm-slim

RUN apt-get update && apt-get install -y --no-install-recommends \
    ca-certificates \
    && rm -rf /var/lib/apt/lists/*

WORKDIR /usr/local/bin
COPY --from=builder /usr/src/sim-rs/target/release/sim-cli .

# Create directory for default files
RUN mkdir -p /usr/local/share/sim-rs

# Copy default configuration and topology
COPY sim-rs/test_data/medium.yaml /usr/local/share/sim-rs/
COPY data/simulation/config.default.yaml /usr/local/share/sim-rs/

# Set default environment variables
ENV DEFAULT_TOPOLOGY=/usr/local/share/sim-rs/medium.yaml
ENV DEFAULT_CONFIG=/usr/local/share/sim-rs/config.default.yaml
ENV DEFAULT_OUTPUT=/output/simulation.jsonl
ENV DEFAULT_SLOTS=1000

# Create output directory
RUN mkdir -p /output
VOLUME /output

ENTRYPOINT ["sim-cli"]
CMD ["/usr/local/share/sim-rs/medium.yaml", \
     "--parameters", "/usr/local/share/sim-rs/config.default.yaml", \
     "--slots", "1000"]