#!/usr/bin/env bash
#
# Prune the given node's immutable DB so the contentious block 67555 is
# not present, then let the node re-fetch whatever we chopped from the
# IOG relay. This replaces the more elaborate seed/truncate step — we
# assume the node's db/immutable/ has already been populated (by an
# external extraction of a leios3-rel-c-1 snapshot, or by a previous
# acceptance run) and only trim the tail.
#
# Invoked once per node in the acceptance harness (see PruneNodeA /
# PruneNodeB in process-compose.yaml). The volatile wipe below is what
# actually forces the node to re-fetch block 67555 fresh from the
# upstream on the next start — see acceptance/README.md.
#
# Algorithm:
#   1. Repeatedly delete the highest-numbered chunk file trio
#      (`.chunk`, `.primary`, `.secondary`) until a plain-bash grep for
#      the contentious block header hash finds no match in any remaining
#      chunk. That hash appears in the immutable DB only as the hbPrev
#      field of block 67556, so its disappearance means block 67555+
#      have been removed from the seeded snapshot.
#   2. Then delete an additional 'EXTRA_CHUNKS_TO_TRIM' chunk trios so
#      NodeA re-fetches a wider band from the upstream. Important once
#      the upstream relays carry the nfrisby hotfix — we want the
#      network path to deliver the *original* bytes of block 67555 (and
#      neighbours) rather than reusing whatever re-encoded copy might
#      have leaked in from an older snapshot state.

set -euo pipefail

: "${NODE_DIR:?NODE_DIR required}"
: "${CONTENTIOUS_HEADER_HASH:=70c34f39cf63c8fe9c0f645ef1c6ea3edcf6f72944af43d3eaaf3b40d252761e}"
: "${MAX_CHUNKS_TO_DELETE:=20}"
# After we've cleared the contentious hash, trim additional chunks so
# NodeA re-fetches a wider band from the upstream. Each chunk covers
# thousands of slots — a handful gives us enough runway to see NodeA
# progress before it hits the contentious block, and (crucially) forces
# the neighbours of block 67555 to come fresh from the (hotfixed) IOG
# relays instead of possibly-stale bytes carried over from the snapshot.
: "${EXTRA_CHUNKS_TO_TRIM:=5}"

IMM_DIR="$NODE_DIR/db/immutable"
VOL_DIR="$NODE_DIR/db/volatile"

for cmd in grep sed printf sort head; do
  if ! command -v "$cmd" >/dev/null 2>&1; then
    echo "prune-immutable: FAIL — required command not on PATH: $cmd" >&2
    exit 1
  fi
done

if [[ ! -d "$IMM_DIR" ]]; then
  # No immutable DB to prune — the node has never run or hasn't been
  # seeded. That's a valid state (fresh NodeB, say); a run-node.sh boot
  # will create everything from genesis. Still wipe volatile below in
  # case a partial volatile dir is lying around from a prior run.
  echo "prune-immutable: no $IMM_DIR to prune; wiping volatile only"
  rm -rf "$VOL_DIR"
  mkdir -p "$VOL_DIR"
  exit 0
fi

# 32 raw bytes of the contentious block's header hash.
hash_bytes=$(printf '%b' "$(sed 's/../\\x&/g' <<<"$CONTENTIOUS_HEADER_HASH")")

contains_contentious() {
  LC_ALL=C grep -laF --binary-files=text -e "$hash_bytes" \
    "$IMM_DIR"/*.chunk 2>/dev/null | head -n1
}

delete_highest_chunk() {
  local top
  top=$(ls "$IMM_DIR"/*.chunk 2>/dev/null | sort | tail -n1) || return 1
  [[ -z "$top" ]] && return 1
  local stem=${top%.chunk}
  echo "prune-immutable: deleting chunk trio ${stem##*/}.{chunk,primary,secondary}"
  rm -f "${stem}.chunk" "${stem}.primary" "${stem}.secondary"
}

# Wipe volatile up front — we want block 67555+ fetched fresh over the
# network so the RB hotfix write path is actually exercised.
rm -rf "$VOL_DIR"
mkdir -p "$VOL_DIR"

# Step 1: iterate until the contentious hash is gone. Bounded so we
# don't nuke the whole DB if something is off.
cleared=""
for _ in $(seq 1 "$MAX_CHUNKS_TO_DELETE"); do
  hit=$(contains_contentious || true)
  if [[ -z "$hit" ]]; then
    echo "prune-immutable: contentious block header hash absent from immutable DB"
    cleared=1
    break
  fi
  echo "prune-immutable: found $CONTENTIOUS_HEADER_HASH in $hit — trimming"
  delete_highest_chunk || {
    echo "prune-immutable: FAIL — no more chunks to delete but hash still present" >&2
    exit 1
  }
done

if [[ -z "$cleared" ]]; then
  echo "prune-immutable: FAIL — hash still present after deleting $MAX_CHUNKS_TO_DELETE chunks" >&2
  echo "                 raise MAX_CHUNKS_TO_DELETE or re-extract a smaller snapshot" >&2
  exit 1
fi

# Step 2: trim additional runway so NodeA re-fetches a wider band from
# the (nfrisby-hotfixed) upstream — see the top-of-file comment.
if (( EXTRA_CHUNKS_TO_TRIM > 0 )); then
  echo "prune-immutable: trimming $EXTRA_CHUNKS_TO_TRIM extra chunk(s) for re-sync runway"
  for _ in $(seq 1 "$EXTRA_CHUNKS_TO_TRIM"); do
    delete_highest_chunk || {
      echo "prune-immutable: no more chunks to delete (asked for $EXTRA_CHUNKS_TO_TRIM extras)"
      break
    }
  done
fi
echo "prune-immutable: done"
