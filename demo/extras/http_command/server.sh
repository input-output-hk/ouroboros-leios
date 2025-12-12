# A simple, single-threaded Bash HTTP server that executes command supplied
# as an argument and returns the output
#
# Dependencies:
# - socat
# - on_request
#
# Usage:
# ./http_command.sh 127.0.0.1 9100 "ls"

# --- Configuration ---
LISTEN_ADDR=${1:-"0.0.0.0"}
LISTEN_PORT=${2:-9100}
COMMAND=${3:-""}
export COMMAND

log() {
  echo "[$(date +'%Y-%m-%d %H:%M:%S')] $1"
}

log "Starting HTTP Command on ${LISTEN_ADDR}:${LISTEN_PORT}..."
log "Command: ${COMMAND}"

socat -d TCP4-LISTEN:"$LISTEN_PORT",bind="$LISTEN_ADDR",reuseaddr,fork SYSTEM:on_request,sigint,nofork
