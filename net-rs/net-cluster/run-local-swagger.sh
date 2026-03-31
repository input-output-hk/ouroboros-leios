#!/usr/bin/env bash
# Run Swagger UI locally via Docker, serving the net-cluster OpenAPI spec.
#
# Usage:
#   cd net-cluster && ./run-local-swagger.sh
#
# Then open http://localhost:8080 in your browser.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
SPEC="$SCRIPT_DIR/OpenAPI.yaml"

if [ ! -f "$SPEC" ]; then
    echo "Error: OpenAPI.yaml not found at $SPEC" >&2
    exit 1
fi

echo "Starting Swagger UI at http://localhost:8080"
echo "Press Ctrl-C to stop."

docker run --rm -p 8080:8080 \
    -e SWAGGER_JSON=/spec/OpenAPI.yaml \
    -v "$SPEC:/spec/OpenAPI.yaml:ro" \
    swaggerapi/swagger-ui
