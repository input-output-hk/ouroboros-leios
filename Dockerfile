FROM debian:bookworm-slim AS base

RUN apt-get update && apt-get install -y --no-install-recommends \
    ca-certificates \
    libgmp10 \
    && rm -rf /var/lib/apt/lists/*

# Create shared directories
RUN mkdir -p /usr/local/share/leios
RUN mkdir -p /output
VOLUME /output

# Copy shared configuration files
COPY data/simulation/config.default.yaml /usr/local/share/leios/config.default.yaml
COPY data/simulation/topo-default-100.yaml /usr/local/share/leios/topology.default.yaml

# Build Rust simulation
FROM rust:1.82-slim AS rust-builder
WORKDIR /usr/src/sim-rs
COPY sim-rs/ .
RUN cargo build --release

# Create Rust simulation image
FROM base AS rust-sim
WORKDIR /output

# Copy the sim-cli binary
COPY --from=rust-builder /usr/src/sim-rs/target/release/sim-cli /usr/local/bin/

# Create entrypoint script
RUN echo '#!/bin/sh\n\
set -e\n\
\n\
# Create output directory if it doesnt exist\n\
mkdir -p /output\n\
\n\
if [ $# -eq 0 ]; then\n\
    exec /usr/local/bin/sim-cli\n\
elif [ $# -eq 1 ] && [ "${1#-}" = "$1" ]; then\n\
    # If only one argument and it doesnt start with -, treat it as output file\n\
    output_dir=$(dirname "$1")\n\
    mkdir -p "$output_dir"\n\
    exec /usr/local/bin/sim-cli /usr/local/share/leios/topology.default.yaml "$1"\n\
else\n\
    # Pass all arguments to sim-cli\n\
    exec /usr/local/bin/sim-cli "$@"\n\
fi' > /usr/local/bin/entrypoint.sh && chmod +x /usr/local/bin/entrypoint.sh

ENTRYPOINT ["/usr/local/bin/entrypoint.sh"]
CMD [] 