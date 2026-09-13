# Checks the proto-devnet Grafana dashboards, demo/proto-devnet/config/dashboards,
# for the things a UI export silently gets wrong.
#
# Scoped to that directory on purpose. Those dashboards are also provisioned by
# cardano-playground from this repo as a flake input, so a broken uid or a stray
# datasource reference here lands on a second, much larger deployment as well as
# on a local devnet. The other Grafana JSON in this repo, antithesis/config and
# demo/extras/x-ray, is local to its own stack and is not checked: the conventions
# below are about being portable across deployments, and those are not shared.
#
# Grafana's "export JSON" writes a dashboard as that Grafana instance saw it, not
# as the repo needs it: the uid becomes whatever that instance assigned, datasource
# references become that instance's internal uids, and a numeric `id` appears. None
# of it fails to parse, none of it is visible in review, and all of it breaks on
# deploy somewhere other than the machine it was exported from. This has landed in
# this directory at least three times.
#
# Hard failures, each one something that breaks a deployment:
#
#   uid != filename     The uid is the dashboard's identity and the /d/<uid> URL.
#                       Changing it stands up a second dashboard and 404s every
#                       existing link rather than updating the one that is there.
#   top-level id        Grafana's internal numeric handle for one instance. It
#                       means nothing anywhere else and can collide on import.
#   unknown datasource  Anything outside the set below is an exporting instance's
#                       private uid, e.g. P8E80F9AEF21F6940. It resolves to nothing
#                       here and the panel is blank with no error.
#   refresh < 1m        The committed refresh is the one every deployment gets, and
#                       these dashboards are shared between a three-node local
#                       devnet and a twenty-five instance cluster. Several carry
#                       twenty-plus Loki panels that each scan logs, so shipping a
#                       5s default is a standing load on the larger deployment for
#                       as long as one browser tab is left open.
#
#                       Only the committed default is checked. The refresh dropdown
#                       is deliberately left alone: sub-minute is a reasonable
#                       choice on a local devnet, and picking it there is a per-user
#                       decision rather than something the repo ships to everyone.
#
# Warnings, cosmetic but worth keeping uniform so dashboards read the same:
# timezone, and auto-refresh being off entirely.
#
# Run it directly, or let .github/workflows/dashboards.yaml run it on any PR that
# touches the dashboards.
set -uo pipefail

SCRIPT_DIR=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
DASH_DIR="${1:-$SCRIPT_DIR/../config/dashboards}"

# Datasources this deployment provisions, plus Grafana's built-ins: -- Grafana --
# for annotations, -- Dashboard -- for a panel reading another panel's result,
# -- Mixed -- for a panel spanning datasources, and __expr__ for a server-side
# expression such as a math over two queries.
#
# Add to this only when a datasource is genuinely provisioned or is a Grafana
# built-in, never to silence a stray export.
ALLOWED_DS='loki mimir __expr__ -- Grafana -- -- Dashboard -- -- Mixed --'

# Shortest auto-refresh a dashboard here may commit to, in seconds.
MIN_REFRESH_SECONDS=60

# Grafana durations: 5s, 30s, 1m, 15m, 1h, 1d. Prints seconds, or -1 if the value
# is not a duration we recognise, which the caller reports rather than ignores.
to_seconds() {
  local v="$1" n u
  n=${v%%[a-z]*}
  u=${v#"$n"}
  case "$n" in
  '' | *[!0-9]*)
    echo -1
    return
    ;;
  esac
  case "$u" in
  ms) echo $((n / 1000)) ;;
  s) echo "$n" ;;
  m) echo $((n * 60)) ;;
  h) echo $((n * 3600)) ;;
  d) echo $((n * 86400)) ;;
  *) echo -1 ;;
  esac
}

fail=0
warn=0

if [ ! -d "$DASH_DIR" ]; then
  echo "check-dashboards: no such directory: $DASH_DIR" >&2
  exit 2
fi

shopt -s nullglob
files=("$DASH_DIR"/*.json)
if [ ${#files[@]} -eq 0 ]; then
  echo "check-dashboards: no dashboards found in $DASH_DIR" >&2
  exit 2
fi

for f in "${files[@]}"; do
  base=$(basename "$f" .json)

  if ! jq -e . "$f" >/dev/null 2>&1; then
    echo "FAIL $base: not valid JSON"
    fail=$((fail + 1))
    continue
  fi

  uid=$(jq -r '.uid // ""' "$f")
  if [ "$uid" != "$base" ]; then
    echo "FAIL $base: uid is \"$uid\", expected \"$base\" to match the filename"
    fail=$((fail + 1))
  fi

  if [ "$(jq -r 'has("id")' "$f")" = "true" ]; then
    echo "FAIL $base: has a top-level \"id\" ($(jq -r '.id' "$f")); remove it"
    fail=$((fail + 1))
  fi

  # Every datasource reference anywhere in the document, panels, targets,
  # templating and annotations alike. Reads anything under a "datasource" key
  # rather than any object carrying a uid: keying on uid+type would miss a bare
  # {"uid": "..."} with no type, which is how some exports write it, and would
  # also pick up the dashboard's own uid.
  #
  # Three shapes are in play. The current one is an object, {"type":..,"uid":..}.
  # Older exports write a bare string naming the datasource, and that form has to
  # be checked too or an instance-private name slips through unseen. A null means
  # "use the org default", which is legitimate, so it is skipped rather than
  # reported as a bad uid.
  #
  # Variable references like $dbsync are fine; they resolve against a
  # datasource-type template variable.
  while IFS= read -r ds; do
    [ -z "$ds" ] && continue
    case "$ds" in
    \$*) continue ;;
    esac
    found=0
    for a in $ALLOWED_DS; do [ "$ds" = "$a" ] && found=1 && break; done
    # ALLOWED_DS entries contain spaces, so re-check the multi-word ones exactly.
    case "$ds" in
    "-- Grafana --" | "-- Dashboard --" | "-- Mixed --") found=1 ;;
    esac
    if [ "$found" -eq 0 ]; then
      echo "FAIL $base: datasource uid \"$ds\" is not provisioned here; expected one of: loki, mimir, or a \$variable"
      fail=$((fail + 1))
    fi
  done < <(jq -r '[.. | objects | select(has("datasource")) | .datasource
                  | if type == "object" then .uid? // empty
                    elif type == "string" then .
                    else empty end] | unique | .[]' "$f")

  tz=$(jq -r '.timezone // ""' "$f")
  if [ "$tz" != "utc" ]; then
    echo "warn $base: timezone is \"$tz\", the rest of this directory uses \"utc\""
    warn=$((warn + 1))
  fi

  refresh=$(jq -r '.refresh // "" | tostring' "$f")
  if [ -z "$refresh" ] || [ "$refresh" = "false" ]; then
    echo "warn $base: auto-refresh is disabled, the rest of this directory uses \"1m\""
    warn=$((warn + 1))
  else
    secs=$(to_seconds "$refresh")
    if [ "$secs" -lt 0 ]; then
      echo "FAIL $base: refresh \"$refresh\" is not a duration this check understands"
      fail=$((fail + 1))
    elif [ "$secs" -lt "$MIN_REFRESH_SECONDS" ]; then
      echo "FAIL $base: refresh is \"$refresh\" (${secs}s), faster than the ${MIN_REFRESH_SECONDS}s floor; every panel re-runs on each tick"
      fail=$((fail + 1))
    fi
  fi

done

echo
echo "check-dashboards: proto-devnet, ${#files[@]} dashboard(s), $fail failure(s), $warn warning(s)"
[ "$fail" -eq 0 ] || exit 1
