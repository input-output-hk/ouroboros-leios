FROM debian:bookworm-slim AS base

RUN apt-get update && apt-get install -y --no-install-recommends \
    ca-certificates \
    libgmp10 \
    libgtk-3-0 \
    libglib2.0-0 \
    libcairo2 \
    libpango-1.0-0 \
    libpangocairo-1.0-0 \
    && rm -rf /var/lib/apt/lists/*

# Create shared directories
RUN mkdir -p /usr/local/share/leios
RUN mkdir -p /output
VOLUME /output

# Copy shared configuration files
COPY data/simulation/config.default.yaml /usr/local/share/leios/config.default.yaml
COPY data/simulation/topo-default-100.yaml /usr/local/share/leios/topology.default.yaml

# Build Rust simulation
FROM rust:1.82-slim AS rs-builder
WORKDIR /usr/src/sim-rs
COPY sim-rs/ .
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
COPY . .

# Build our simulation with verbose output
WORKDIR /build/simulation
RUN cabal update && \
    cabal build -v3 all && \
    find /build -name "ols" -type f -executable

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
COPY --from=hs-builder /build/dist-newstyle/build/aarch64-linux/ghc-9.8.2/ouroboros-leios-sim-0.1.0.0/x/ols/build/ols/ols /usr/local/bin/

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

# Create combined image with both simulations
FROM base AS all
WORKDIR /output

# Copy both binaries
COPY --from=rs-builder /usr/src/sim-rs/target/release/sim-cli /usr/local/bin/
COPY --from=hs-builder /build/dist-newstyle/build/aarch64-linux/ghc-9.8.2/ouroboros-leios-sim-0.1.0.0/x/ols/build/ols/ols /usr/local/bin/

# Copy both entrypoint scripts
COPY --from=rs /usr/local/bin/entrypoint-rs.sh /usr/local/bin/
COPY --from=hs /usr/local/bin/entrypoint-hs.sh /usr/local/bin/

# Create wrapper entrypoint script
RUN echo '#!/bin/sh\n\
set -e\n\
\n\
# Check which simulation to run\n\
if [ "$1" = "rs" ]; then\n\
    shift\n\
    exec /usr/local/bin/entrypoint-rs.sh "$@"\n\
elif [ "$1" = "hs" ]; then\n\
    shift\n\
    exec /usr/local/bin/entrypoint-hs.sh "$@"\n\
else\n\
    echo "Usage: docker run ... [rs|hs] [simulation args...]"\n\
    echo "  rs: Run Rust simulation"\n\
    echo "  hs: Run Haskell simulation"\n\
    exit 1\n\
fi' > /usr/local/bin/entrypoint.sh && chmod +x /usr/local/bin/entrypoint.sh

ENTRYPOINT ["/usr/local/bin/entrypoint-rs.sh"]
CMD []

# Create Haskell simulation image
FROM base AS hs
WORKDIR /output

# Copy the ols binary and necessary files
COPY --from=hs-builder /build/dist-newstyle/build/aarch64-linux/ghc-9.8.2/ouroboros-leios-sim-0.1.0.0/x/ols/build/ols/ols /usr/local/bin/

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