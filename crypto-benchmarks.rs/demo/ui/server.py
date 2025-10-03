from flask import Flask, jsonify, render_template, redirect, url_for
import os, json

app = Flask(__name__, static_folder="static", template_folder="templates")

# Resolve demo root (one level up from this `ui` folder)
HERE = os.path.abspath(os.path.dirname(__file__))
DEMO_ROOT = os.path.abspath(os.path.join(HERE, ".."))

# === Example endpoint for cert JSON ===
@app.route("/cert/<run>")
def cert(run):
    # Load certificate.pretty.json from ../<run>/certificate.pretty.json
    # so it works regardless of the current working directory
    rel_path = os.path.join(run, "certificate.pretty.json")
    path = os.path.join(DEMO_ROOT, rel_path)
    if not os.path.isfile(path):
        return jsonify({
            "error": "certificate.pretty.json not found",
            "run": run,
            "looked_for": path
        }), 404
    with open(path, "r", encoding="utf-8") as f:
        data = json.load(f)
    return jsonify(data)

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