from flask import (
    Flask,
    send_from_directory,
    jsonify,
    render_template,
    abort,
    redirect,
    url_for,
)
import json
import subprocess
from pathlib import Path

import cbor2


app = Flask(__name__, static_folder="static", template_folder="templates")
ROOT = Path(__file__).resolve().parent.parent


def run_dir_path(run: str) -> Path:
    return ROOT / run


@app.route("/committee/<run>")
def committee(run):
    rdir = run_dir_path(run)
    script = ROOT / "scripts" / "extract_committee.py"
    if not script.is_file():
        abort(500, f"extract_committee.py not found at {script}")

    try:
        out = subprocess.check_output(
            ["python3", str(script), str(rdir)], cwd=ROOT, text=True
        )
        data = json.loads(out)
        return jsonify(data)
    except subprocess.CalledProcessError as e:
        abort(500, f"extract_committee failed: {e.output or e}")


@app.route("/registry/<run>")
def registry(run):
    """Return pool list + stakes (best-effort)."""
    d = run_dir_path(run)
    stake_path = d / "stake.cbor"
    pools = []
    total_stake = 0

    if stake_path.is_file():
        with stake_path.open("rb") as f:
            stake = cbor2.load(f)
            # stake is likely a map {poolId(bytes|hex): int stake}
            if isinstance(stake, dict):
                for k, v in stake.items():
                    pid = k.hex() if isinstance(k, (bytes, bytearray)) else str(k)
                    s = int(v) if isinstance(v, int) else 0
                    pools.append({"id": pid, "stake": s})
                    total_stake += s

    return jsonify(
        {"pools": pools, "total_pools": len(pools), "total_stake": total_stake}
    )


@app.route("/demo/<run>")
def demo_for_run(run):
    """Serve demo.json from the given run directory."""
    run_dir = run_dir_path(run)
    demo_path = run_dir / "demo.json"
    if demo_path.is_file():
        return send_from_directory(str(run_dir), "demo.json")
    abort(404, f"demo.json not found in {run_dir}")


@app.route("/demo/<run>/<path:filename>")
def demo_asset(run, filename):
    """Serve auxiliary files (eid.txt, ebhash.txt, etc.) from the run directory."""
    run_dir = run_dir_path(run)
    target_path = run_dir / filename
    if target_path.is_file():
        return send_from_directory(str(run_dir), filename)
    abort(404, f"{filename} not found in {run_dir}")


# === UI endpoint ===
@app.route("/ui")
def ui():
    return render_template("index.html")


# Small helper route to redirect `/` to `/ui`
@app.route("/")
def root():
    return redirect(url_for("ui"))


if __name__ == "__main__":
    app.run(host="0.0.0.0", port=5050, debug=True)
