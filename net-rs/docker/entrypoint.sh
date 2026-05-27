#!/bin/sh
# Render a runtime overlay TOML from env vars and exec net-node.
#
# Env contract:
#   NET_NODE_LISTEN_PORT  default 3001; binds 0.0.0.0:$PORT.
#   NET_NODE_PEERS        optional CSV of host:port outbound peers.
#   NET_NODE_ID           optional logical node identifier.
#   NET_NODE_CONFIG       optional absolute path to a user TOML overlay
#                         (applied last, wins everything).
#   RUST_LOG              default info.
set -eu

LISTEN_PORT="${NET_NODE_LISTEN_PORT:-3001}"
export RUST_LOG="${RUST_LOG:-info}"

OVERLAY=/run/net-node/overlay.toml
TMP="${OVERLAY}.tmp"
: > "$TMP"

printf 'listen_address = "0.0.0.0:%s"\n' "$LISTEN_PORT" >> "$TMP"

if [ -n "${NET_NODE_ID:-}" ]; then
    # Reject characters that would need TOML escaping; the overlay is
    # written by printf into a "%s" template and net-node would surface
    # any breakage as an opaque TOML parse error at startup.
    case "$NET_NODE_ID" in
        *[!A-Za-z0-9._-]*)
            echo "entrypoint: NET_NODE_ID=\"$NET_NODE_ID\" must match [A-Za-z0-9._-]+" >&2
            exit 64
            ;;
    esac
    printf 'node_id = "%s"\n' "$NET_NODE_ID" >> "$TMP"
fi

# [[peers]] is an array-of-tables; net-node's --set only handles flat
# scalars, so peers must come from a file. Render one block per CSV entry.
if [ -n "${NET_NODE_PEERS:-}" ]; then
    OLD_IFS=$IFS
    IFS=','
    set -f                # block pathname expansion on the unquoted split
    # shellcheck disable=SC2086
    set -- $NET_NODE_PEERS
    set +f
    IFS=$OLD_IFS
    for entry in "$@"; do
        addr=$(printf '%s' "$entry" | sed -e 's/^[[:space:]]*//' -e 's/[[:space:]]*$//')
        [ -z "$addr" ] && continue
        {
            printf '\n[[peers]]\n'
            printf 'address = "%s"\n' "$addr"
        } >> "$TMP"
    done
fi

mv "$TMP" "$OVERLAY"

set -- --config /etc/leios/mainnet.toml \
       --config /etc/leios/relay.toml \
       --config "$OVERLAY"

if [ -n "${NET_NODE_CONFIG:-}" ]; then
    if [ ! -r "$NET_NODE_CONFIG" ]; then
        echo "entrypoint: NET_NODE_CONFIG=$NET_NODE_CONFIG is not readable" >&2
        exit 64
    fi
    set -- "$@" --config "$NET_NODE_CONFIG"
fi

# exec so SIGTERM reaches net-node directly; main.rs handles ctrl_c().
exec /usr/local/bin/net-node "$@"
