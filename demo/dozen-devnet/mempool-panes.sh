#!/usr/bin/env bash
# Twelve mempool-monitor panes in one tiled tmux window, one per node.
#
# The window is attached to a tmux session that is already running -- the current
# one when invoked from inside tmux, otherwise the first the server reports. The
# devnet usually already owns a session, and a second one would just hide these
# panes behind a detach. A session is only started when no tmux server is running
# at all, since then there is nothing to attach to.
#
# process-compose cannot tile: its TUI shows a process list plus one pane at a
# time, so `is_interactive` gets you a real TTY but not twelve of them side by
# side. Hence tmux, and hence on-demand rather than part of the devnet.
#
# tmux's tiled layout grows rows and columns alternately until rows * columns
# covers the pane count, so twelve panes is always 4 rows x 3 columns whatever the
# terminal size. Pane order therefore fills column-major on purpose: each column
# is one block producer's group, its producer on top and its three relays below.
#
# So fragmentation reads down a column (does this group's own colour dominate its
# own relays) and across a row (has it leaked to the others).
set -euo pipefail

# Session to attach to, when set and it exists; otherwise one is chosen. Also the
# name used if a session has to be started because no server is running.
: "${SESSION:=}"
# Window created within it. One per invocation, so several devnets can coexist.
: "${WINDOW:=mempools}"
SOURCE_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
: "${WORKING_DIR:=${SOURCE_DIR}/tmp-devnet}"
: "${MEMPOOL_MONITOR:=mempool-monitor}"
# Period between snapshot starts, not a gap after each drain. Drains measure 1-3 s
# against the 5 MB cap, so 5 s keeps a node iterated well under half the time. A
# drain that overruns just runs back-to-back rather than stretching the cadence.
: "${MONITOR_INTERVAL:=5}"
: "${MAGIC:=164}"
# Must match the generators; same defaults as run.sh.
: "${COLOR1:=ff0000}"
: "${COLOR2:=00a0ff}"
: "${COLOR3:=ffd000}"
# Whether each pane also appends its snapshots to a TSV.
: "${TSV:=1}"

# Ordered so a 4x3 tiled layout puts one group per column: the producers fill the
# first row, then each group's relays run down beneath its producer. Override for
# a different devnet, e.g. NODES="node1 node2 node3" against proto-devnet.
: "${NODES:=bp1 bp2 bp3 relay11 relay21 relay31 relay12 relay22 relay32 relay13 relay23 relay33}"
read -ra NODES <<<"$NODES"

for cmd in tmux "$MEMPOOL_MONITOR"; do
	if ! command -v "$cmd" &>/dev/null; then
		echo "Error: $cmd not found on PATH" >&2
		echo "(both come from the dev shell: nix develop .#dev-demo-dozen-devnet)" >&2
		exit 1
	fi
done

if [ ! -d "$WORKING_DIR" ]; then
	echo "Error: $WORKING_DIR does not exist — start the devnet first" >&2
	exit 1
fi

# A node's own colour is its block producer's generator: bp2 and relay21..23 all
# count COLOR2 as local.
own_color() {
	local digits="${1#bp}"
	digits="${digits#relay}"
	local var="COLOR${digits:0:1}"
	echo "${!var}"
}

monitor_cmd() {
	local name="$1" tsv=""
	if [ "$TSV" = "1" ]; then
		tsv="--tsv ${WORKING_DIR}/mempool-${name}.tsv"
	fi
	printf '%s --socket-path %s --testnet-magic %s --label %s --own-color %s --interval %s %s' \
		"$MEMPOOL_MONITOR" \
		"${WORKING_DIR}/${name}/node.socket" \
		"$MAGIC" \
		"$name" \
		"$(own_color "$name")" \
		"$MONITOR_INTERVAL" \
		"$tsv"
}

# Prefer the session the user is looking at, then an explicit SESSION, then
# whatever the server happens to have.
pick_session() {
	if [ -n "${TMUX:-}" ]; then
		tmux display-message -p '#S'
	elif [ -n "$SESSION" ] && tmux has-session -t "$SESSION" 2>/dev/null; then
		echo "$SESSION"
	else
		tmux list-sessions -F '#S' 2>/dev/null | head -1
	fi
}

target="$(pick_session)"
if [ -z "$target" ]; then
	target="${SESSION:-mempool}"
	echo "No tmux session running; starting '$target'."
	tmux new-session -d -s "$target"
fi

if tmux list-windows -t "$target" -F '#W' 2>/dev/null | grep -qxF "$WINDOW"; then
	echo "Window '$WINDOW' already exists in session '$target'; selecting it. Kill it with:"
	echo "  tmux kill-window -t $target:$WINDOW"
else
	# The trailing colon matters: new-window's -t is a target-*window*, so a bare
	# session name resolves to that session's current window and tries to create
	# at its index ("index N in use"). "session:" means the session itself, and
	# tmux picks the next free index.
	tmux new-window -t "${target}:" -n "$WINDOW" "$(monitor_cmd "${NODES[0]}")"
	# Leave a dead monitor's output on screen rather than collapsing the pane, so a
	# failure is readable instead of just missing. Window-scoped: the session is
	# not ours to reconfigure, so no session-wide options are touched.
	tmux set-option -w -t "$target:$WINDOW" remain-on-exit on

	for name in "${NODES[@]:1}"; do
		tmux split-window -t "$target:$WINDOW" "$(monitor_cmd "$name")"
		# Re-tile as we go: splitting a pane that has become too small to halve fails.
		tmux select-layout -t "$target:$WINDOW" tiled >/dev/null
	done

	tmux select-layout -t "$target:$WINDOW" tiled >/dev/null
fi

tmux select-pane -t "$target:$WINDOW.0"
tmux select-window -t "$target:$WINDOW"

cat <<EOF
Twelve monitors in window '$WINDOW' of tmux session '$target'.

  columns are groups:   bp1      bp2      bp3
                        relay11  relay21  relay31
                        relay12  relay22  relay32
                        relay13  relay23  relay33

  zoom one pane     ctrl-b z
  next/prev window  ctrl-b n / ctrl-b p
  detach            ctrl-b d
  kill just these   tmux kill-window -t $target:$WINDOW

Each pane needs about 50x10; below that the panes will be clipped, so a wide
terminal or a smaller subset of NODES is the way.
EOF

# Already inside tmux, the select-window above is all that is needed; attaching
# from within would nest a client in itself.
if [ -z "${TMUX:-}" ]; then
	exec tmux attach -t "$target"
fi
