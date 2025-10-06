from flask import Flask, send_from_directory, jsonify, render_template, request, abort
import os, json, subprocess
import cbor2

app = Flask(__name__, static_folder="static", template_folder="templates")

app = Flask(__name__, static_folder="static", template_folder="templates")
ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), ".."))

def run_dir_path(run):
    return os.path.join(ROOT, run)

def pretty_json_path(run):
    return os.path.join(run_dir_path(run), "certificate.pretty.json")


def regenerate_pretty(run: str, all_voters: bool) -> None:
    """
    Re-generate certificate.pretty.json by invoking our pretty script.
    We call the Python module directly to avoid shell pitfalls.
    """
    rdir = run_dir_path(run)
    cert = os.path.join(rdir, "certificate.cbor")
    votes = os.path.join(rdir, "votes.cbor")
    script = os.path.join(ROOT, "scripts", "pretty_cert.py")
    if not os.path.isfile(script):
        abort(500, f"pretty_cert.py not found at {script}")
    if not os.path.isfile(cert):
        abort(404, f"certificate.cbor not found in {rdir}")

    args = [ "python3", script, cert, votes ]
    if all_voters:
        args.append("--all-voters")

    # Write to certificate.pretty.json
    out_path = pretty_json_path(run)
    try:
        out = subprocess.check_output(args, cwd=ROOT, text=True)
        with open(out_path, "w") as f:
            f.write(out)
    except subprocess.CalledProcessError as e:
        abort(500, f"pretty_cert.py failed: {e.output or e}")

@app.route("/committee/<run>")
def committee(run):
    rdir = run_dir_path(run)
    script = os.path.join(ROOT, "scripts", "extract_committee.py")
    if not os.path.isfile(script):
        abort(500, f"extract_committee.py not found at {script}")

    try:
        out = subprocess.check_output(["python3", script, rdir], cwd=ROOT, text=True)
        data = json.loads(out)
        return jsonify(data)
    except subprocess.CalledProcessError as e:
        abort(500, f"extract_committee failed: {e.output or e}")


@app.route("/registry/<run>")
def registry(run):
    """Return pool list + stakes (best-effort)."""
    d = run_dir_path(run)
    stake_path = os.path.join(d, "stake.cbor")
    pools = []
    total_stake = 0

    if os.path.isfile(stake_path):
        with open(stake_path, "rb") as f:
            stake = cbor2.load(f)
            # stake is likely a map {poolId(bytes|hex): int stake}
            if isinstance(stake, dict):
                for k, v in stake.items():
                    pid = k.hex() if isinstance(k, (bytes, bytearray)) else str(k)
                    s = int(v) if isinstance(v, int) else 0
                    pools.append({"id": pid, "stake": s})
                    total_stake += s

    return jsonify({
        "pools": pools,
        "total_pools": len(pools),
        "total_stake": total_stake
    })

@app.route("/votes/<run>")
def votes(run):
    """Expose elected voter IDs (first pass: read from certificate.pretty.json)."""
    d = run_dir_path(run)
    cert_path = os.path.join(d, "certificate.pretty.json")
    voters = []
    pv = []
    npv = []
    if os.path.isfile(cert_path):
        with open(cert_path) as f:
            c = json.load(f)
        # prefer full lists if present, else samples
        pv = c.get("persistent_voters") or []
        npv = c.get("nonpersistent_voters") or c.get("nonpersistent_voters_sample") or []
        voters = (pv or []) + (npv or [])

    return jsonify({
        "elected": voters,
        "persistent": pv,
        "nonpersistent": npv
    })

@app.route("/cert/<run>")
def cert(run):
    all_flag = request.args.get("all") == "1"
    # If 'all=1' is requested or pretty.json is missing, regenerate
    if all_flag or not os.path.isfile(pretty_json_path(run)):
        regenerate_pretty(run, all_voters=all_flag)

    try:
        with open(pretty_json_path(run)) as f:
            data = json.load(f)
        return jsonify(data)
    except FileNotFoundError:
        abort(404, f"certificate.pretty.json not found for {run}")

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