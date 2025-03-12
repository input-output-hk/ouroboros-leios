FROM debian:bookworm-slim AS base

# Create shared directories and install dependencies in one layer
RUN apt-get update && apt-get install -y --no-install-recommends \
    ca-certificates \
    libgmp10 \
    libgtk-3-0 \
    libglib2.0-0 \
    libcairo2 \
    libpango-1.0-0 \
    libpangocairo-1.0-0 \
    && rm -rf /var/lib/apt/lists/* \
    && mkdir -p /usr/local/share/leios \
    && mkdir -p /output

VOLUME /output

# Copy shared configuration files
COPY data/simulation/config.default.yaml /usr/local/share/leios/config.default.yaml
COPY data/simulation/topo-default-100.yaml /usr/local/share/leios/topology.default.yaml

# Build Rust simulation
FROM rust:1.82-slim AS rs-builder
WORKDIR /usr/src/sim-rs
COPY sim-rs/ .
COPY /data/simulation/config.default.yaml parameters/
RUN cargo build --release

# Build Haskell simulation
FROM haskell:9.8.2-slim AS hs-builder
WORKDIR /build

# Install git, SSL certificates, and GTK3 development dependencies
RUN apt-get update && \
    apt-get install -y \
        git \
        ca-certificates \
        curl \
        pkg-config \
        libgtk-3-dev \
        libcairo2-dev \
        libpango1.0-dev \
        libgmp-dev \
        libtinfo-dev \
        zlib1g-dev \
    && rm -rf /var/lib/apt/lists/*

# Copy project files
COPY simulation /build/simulation/
COPY conformance-testing /build/conformance-testing/
COPY leios-trace-hs /build/leios-trace-hs/
COPY cabal.project /build/

# Build simulation
WORKDIR /build
RUN cabal update && \
    cabal build all && \
    find /build/dist-newstyle -type f -name "ols" -exec cp {} /build/ols \;

# Create Rust simulation image
FROM base AS rs
WORKDIR /output

# Copy the sim-cli binary
COPY --from=rs-builder /usr/src/sim-rs/target/release/sim-cli /usr/local/bin/

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
fi' > /usr/local/bin/entrypoint-rs.sh && chmod +x /usr/local/bin/entrypoint-rs.sh

ENTRYPOINT ["/usr/local/bin/entrypoint-rs.sh"]
CMD []

# Create Haskell simulation image
FROM base AS hs
WORKDIR /output

# Copy the ols binary and necessary files
COPY --from=hs-builder /build/ols /usr/local/bin/

# Create entrypoint script for Haskell simulation
RUN echo '#!/bin/sh\n\
set -e\n\
\n\
# Create output directory if it doesnt exist\n\
mkdir -p /output\n\
\n\
# Default values\n\
TOPOLOGY_FILE="/usr/local/share/leios/topology.default.yaml"\n\
CONFIG_FILE="/usr/local/share/leios/config.default.yaml"\n\
OUTPUT_SECONDS=40\n\
SEED=0\n\
\n\
# Parse arguments\n\
while [ $# -gt 0 ]; do\n\
    case "$1" in\n\
        --topology|-t)\n\
            TOPOLOGY_FILE="$2"\n\
            shift 2\n\
            ;;\n\
        --config|-l)\n\
            CONFIG_FILE="$2"\n\
            shift 2\n\
            ;;\n\
        --output-seconds)\n\
            OUTPUT_SECONDS="$2"\n\
            shift 2\n\
            ;;\n\
        --seed)\n\
            SEED="$2"\n\
            shift 2\n\
            ;;\n\
        --output-file)\n\
            OUTPUT_FILE="$2"\n\
            shift 2\n\
            ;;\n\
        *)\n\
            break\n\
            ;;\n\
    esac\n\
done\n\
\n\
if [ -z "$OUTPUT_FILE" ]; then\n\
    TIMESTAMP=$(date +%Y%m%d_%H%M%S)\n\
    OUTPUT_FILE="/output/simulation_${TIMESTAMP}.log"\n\
fi\n\
\n\
# Create a temporary file\n\
TEMP_FILE="${OUTPUT_FILE}.tmp"\n\
\n\
# Ensure output directory exists\n\
mkdir -p "$(dirname "$OUTPUT_FILE")"\n\
\n\
# Run simulation with arguments, writing to temp file\n\
/usr/local/bin/ols sim short-leios \\\n\
    --seed "$SEED" \\\n\
    --leios-config-file "$CONFIG_FILE" \\\n\
    --topology-file "$TOPOLOGY_FILE" \\\n\
    --output-seconds "$OUTPUT_SECONDS" \\\n\
    --output-file "$TEMP_FILE" \\\n\
    "$@" && \\\n\
mv "$TEMP_FILE" "$OUTPUT_FILE"' > /usr/local/bin/entrypoint-hs.sh && chmod +x /usr/local/bin/entrypoint-hs.sh

ENTRYPOINT ["/usr/local/bin/entrypoint-hs.sh"]
CMD [] 
