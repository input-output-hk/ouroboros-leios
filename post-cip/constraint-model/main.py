import json
import sys
import csv
import argparse
import networkx as nx
from ortools.sat.python import cp_model

# Optional imports for visualization
try:
    import yaml
except ImportError:
    yaml = None

try:
    import matplotlib.pyplot as plt
    import matplotlib.patches as mpatches

    MATPLOTLIB_AVAILABLE = True
except ImportError:
    MATPLOTLIB_AVAILABLE = False


# ==========================================
# 1. IO UTILITIES (JSON & YAML)
# ==========================================
def read_scenario(filepath):
    """
    Reads parameters and DAG from a JSON or YAML file.
    Supports .json, .yaml, and .yml extensions.
    """
    if filepath.lower().endswith((".yaml", ".yml")):
        if yaml is None:
            print(
                "Error: PyYAML library is missing. Please install it via 'pip install pyyaml'"
            )
            sys.exit(1)
        with open(filepath, "r") as f:
            data = yaml.safe_load(f)
    else:
        with open(filepath, "r") as f:
            data = json.load(f)

    if "parameters" not in data:
        raise ValueError(
            f"Input file '{filepath}' is missing the 'parameters' section."
        )
    if "dag" not in data:
        raise ValueError(f"Input file '{filepath}' is missing the 'dag' section.")

    params = data["parameters"]
    raw_dag = data["dag"]

    # Validate Global Parameters
    required_params = ["n_cpu", "delta_rh", "delta_rb", "delta_eh", "cost_vote"]
    for p in required_params:
        if p not in params:
            raise ValueError(f"Missing required global parameter '{p}'.")

    # Global defaults
    default_verify = params.get("cost_verify")
    default_apply = params.get("cost_apply")

    G = nx.DiGraph()

    for tx_hash, attrs in raw_dag.items():
        node_type = attrs.get("type")
        if not node_type:
            raise ValueError(
                f"Transaction '{tx_hash}' missing required attribute 'type'."
            )

        # --- LG (Ledger) Nodes ---
        if node_type == "LG":
            # LG nodes are roots/state. They don't need costs or delays.
            G.add_node(tx_hash, type="LG")
            # LG nodes typically don't have inputs, but if they do, we ignore them or process them.
            # Here we assume they are roots.
            continue

        # --- RB / EH Nodes ---
        # These require full attributes
        if "arrival_delay" not in attrs:
            raise ValueError(
                f"Transaction '{tx_hash}' ({node_type}) missing 'arrival_delay'."
            )

        # Resolve Costs
        cost_verify = attrs.get("cost_verify")
        if cost_verify is None:
            if default_verify is not None:
                cost_verify = default_verify
            else:
                raise ValueError(f"Transaction '{tx_hash}' missing 'cost_verify'.")

        cost_apply = attrs.get("cost_apply")
        if cost_apply is None:
            if default_apply is not None:
                cost_apply = default_apply
            else:
                raise ValueError(f"Transaction '{tx_hash}' missing 'cost_apply'.")

        G.add_node(
            tx_hash,
            type=node_type,
            arrival_delay=attrs["arrival_delay"],
            cost_verify=cost_verify,
            cost_apply=cost_apply,
        )

        # Process Inputs (Dependencies)
        # Expected format: "inputs": ["parent_hash1", "parent_hash2"]
        inputs = attrs.get("inputs", [])

        if not isinstance(inputs, list):
            raise ValueError(
                f"Attribute 'inputs' for '{tx_hash}' must be a list of strings."
            )

        for parent_hash in inputs:
            # Add dependency: Parent -> Current
            G.add_edge(parent_hash, tx_hash)

    return params, G


def generate_dummy_file(filepath):
    """Generates a sample scenario file."""
    data = {
        "parameters": {
            "n_cpu": 2,
            "delta_rh": 10000,
            "delta_rb": 5000,
            "delta_eh": 5000,
            "cost_verify": 4000,
            "cost_apply": 6000,
            "cost_vote": 2000,
        },
        "dag": {
            # --- LG (Previous Ledger State) ---
            "0xUTXO_1": {"type": "LG"},
            "0xUTXO_2": {"type": "LG"},
            # --- RB TRANSACTIONS ---
            # Now inputs are lists of hash strings
            "0xRB_Tx1": {
                "type": "RB",
                "arrival_delay": 0,
                "inputs": ["0xUTXO_1"],
                "cost_verify": 3500,
                "cost_apply": 5500,
            },
            "0xRB_Tx2": {"type": "RB", "arrival_delay": 0, "inputs": ["0xUTXO_2"]},
            # --- EH TRANSACTIONS ---
            "0xEH_Tx1": {
                "type": "EH",
                "arrival_delay": 2000,
                "inputs": ["0xRB_Tx1", "0xRB_Tx2"],
                "cost_verify": 4200,
                "cost_apply": 6100,
            },
            "0xEH_Tx2": {"type": "EH", "arrival_delay": 8000, "inputs": ["0xRB_Tx2"]},
            "0xEH_Tx3": {"type": "EH", "arrival_delay": 12000, "inputs": ["0xEH_Tx1"]},
        },
    }

    with open(filepath, "w") as f:
        if filepath.lower().endswith((".yaml", ".yml")):
            if yaml is None:
                print("Error: PyYAML is missing.")
                sys.exit(1)
            yaml.dump(data, f, sort_keys=False, default_flow_style=False)
        else:
            json.dump(data, f, indent=2)

    print(f"Generated sample file: {filepath}")


# ==========================================
# 2. STATISTICS & OUTPUT
# ==========================================
def calculate_statistics(makespan, tasks, params):
    n_cpu = params["n_cpu"]
    total_capacity = makespan * n_cpu
    total_work = sum(t["end"] - t["start"] for t in tasks)

    stats = {
        "makespan": makespan,
        "n_cpu": n_cpu,
        "total_capacity_cycles": total_capacity,
        "total_work_cycles": total_work,
        "cpu_utilization": total_work / total_capacity if total_capacity > 0 else 0.0,
    }

    phases = ["Ver", "App", "Vote"]
    phase_stats = {}

    for p in phases:
        p_tasks = [t for t in tasks if t["type"] == p]
        if not p_tasks:
            phase_stats[p] = {
                "work_cycles": 0,
                "fraction_of_total_work": 0.0,
                "avg_parallelism": 0.0,
            }
            continue

        work = sum(t["end"] - t["start"] for t in p_tasks)
        start_t = min(t["start"] for t in p_tasks)
        end_t = max(t["end"] for t in p_tasks)
        wallclock_dur = end_t - start_t

        phase_stats[p] = {
            "work_cycles": work,
            "fraction_of_total_work": work / total_work if total_work > 0 else 0.0,
            "avg_parallelism": work / wallclock_dur if wallclock_dur > 0 else 0.0,
            "phase_wallclock_duration": wallclock_dur,
        }
    stats["phases"] = phase_stats

    # Wallclock Idle Time
    sorted_tasks = sorted(tasks, key=lambda x: x["start"])
    active_ranges = []

    if sorted_tasks:
        curr_start, curr_end = sorted_tasks[0]["start"], sorted_tasks[0]["end"]
        for t in sorted_tasks[1:]:
            if t["start"] < curr_end:
                curr_end = max(curr_end, t["end"])
            else:
                active_ranges.append((curr_start, curr_end))
                curr_start, curr_end = t["start"], t["end"]
        active_ranges.append((curr_start, curr_end))

    total_active_wallclock = sum(end - start for start, end in active_ranges)
    wallclock_idle = makespan - total_active_wallclock

    stats["wallclock_idle"] = wallclock_idle
    stats["fraction_wallclock_idle"] = (
        wallclock_idle / makespan if makespan > 0 else 0.0
    )

    return stats


def compute_schedule(solver, meta, intervals, makespan_var, params):
    tasks = []
    for iv in intervals:
        name = iv.Name()
        if name in meta:
            start = solver.Value(iv.StartExpr())
            end = solver.Value(iv.EndExpr())
            info = meta[name]
            tasks.append(
                {
                    "start": start,
                    "end": end,
                    "desc": f"{info['type']} {info['id']}",
                    "type": info["type"],
                    "raw_id": info["id"],
                }
            )

    tasks.sort(key=lambda x: x["start"])
    cpu_timeline = [0] * params["n_cpu"]

    for t in tasks:
        assigned = 0
        for c in range(params["n_cpu"]):
            if cpu_timeline[c] <= t["start"]:
                assigned = c
                break
        t["cpu"] = assigned
        cpu_timeline[assigned] = t["end"]

    return solver.Value(makespan_var), tasks


def print_schedule_table(tasks, file=sys.stdout):
    print("\nSCHEDULE TABLE", file=file)
    print("-" * 75, file=file)
    print(f"{'CPU':<4} | {'Time (µs)':<15} | {'Task'}", file=file)
    print("-" * 75, file=file)
    tasks_sorted = sorted(tasks, key=lambda x: (x["cpu"], x["start"]))
    for t in tasks_sorted:
        time_str = f"{t['start']} -> {t['end']}"
        print(f"{t['cpu']:<4} | {time_str:<15} | {t['desc']}", file=file)


def print_statistics(makespan, stats, file=sys.stderr):
    print(f"\nFinal t1 (Makespan): {makespan} µs", file=file)
    print("=" * 40, file=file)
    print("PERFORMANCE STATISTICS", file=file)
    print("=" * 40, file=file)
    print(f"CPU Utilization:       {stats['cpu_utilization']:.1%}", file=file)
    print(
        f"Wallclock Idle:        {stats['fraction_wallclock_idle']:.1%} ({stats['wallclock_idle']} µs)",
        file=file,
    )
    print("-" * 40, file=file)
    print(f"{'Phase':<6} | {'Work %':<8} | {'Parallelism':<11}", file=file)
    print("-" * 40, file=file)
    for p, data in stats["phases"].items():
        print(
            f"{p:<6} | {data['fraction_of_total_work']:<8.1%} | {data['avg_parallelism']:<11.2f}",
            file=file,
        )
    print("=" * 40, file=file)


def write_schedule_yaml(filepath, makespan, tasks, params, stats):
    if yaml is None:
        return
    output_data = {"parameters": params, "statistics": stats, "schedule": []}
    tasks_sorted = sorted(tasks, key=lambda x: x["start"])
    for t in tasks_sorted:
        output_data["schedule"].append(
            {
                "id": t["raw_id"],
                "type": t["type"],
                "cpu": t["cpu"],
                "start": t["start"],
                "end": t["end"],
                "duration": t["end"] - t["start"],
            }
        )
    with open(filepath, "w") as f:
        yaml.dump(output_data, f, sort_keys=False, default_flow_style=False)
    print(f"YAML results written to: {filepath}")


def write_chrome_trace(filepath, tasks):
    trace_events = []

    # 1. Anchor Event: Force timeline to start at 0
    trace_events.append(
        {
            "name": "Block Produced",
            "cat": "__metadata",
            "ph": "I",  # Instant Event
            "ts": 0,
            "pid": 1,
            "tid": 0,
            "s": "g",  # Global scope
            "args": {"desc": "T=0 Anchor"},
        }
    )

    # 2. Task Events
    for t in tasks:
        # Scale = 1 because units are already microseconds
        scale = 1
        event = {
            "name": t["desc"],
            "cat": t["type"],
            "ph": "X",
            "ts": t["start"] * scale,
            "dur": (t["end"] - t["start"]) * scale,
            "pid": 1,
            "tid": t["cpu"],
            "args": {"raw_id": str(t["raw_id"])},
        }
        trace_events.append(event)

    wrapper = {"traceEvents": trace_events}
    with open(filepath, "w") as f:
        json.dump(wrapper, f)
    print(f"Chrome Trace written to: {filepath}")


def write_csv(filepath, tasks):
    with open(filepath, "w", newline="") as f:
        writer = csv.writer(f)
        writer.writerow(
            ["TaskID", "Type", "Description", "CPU", "Start", "End", "Duration"]
        )
        for t in tasks:
            writer.writerow(
                [
                    t["raw_id"],
                    t["type"],
                    t["desc"],
                    t["cpu"],
                    t["start"],
                    t["end"],
                    t["end"] - t["start"],
                ]
            )
    print(f"CSV results written to: {filepath}")


def plot_gantt(tasks, makespan, params, filename="gantt.png"):
    if not MATPLOTLIB_AVAILABLE:
        print("Warning: Matplotlib not installed. Skipping Gantt chart.")
        return

    fig, ax = plt.subplots(figsize=(12, 6))
    colors = {"Ver": "tab:blue", "App": "tab:orange", "Vote": "tab:green"}
    legend_patches = [mpatches.Patch(color=v, label=k) for k, v in colors.items()]

    for t in tasks:
        c = colors.get(t["type"], "gray")
        ax.broken_barh(
            [(t["start"], t["end"] - t["start"])],
            (t["cpu"] - 0.4, 0.8),
            facecolors=c,
            edgecolors="white",
        )

        if (t["end"] - t["start"]) > 2:
            mid_x = t["start"] + (t["end"] - t["start"]) / 2
            mid_y = t["cpu"]
            ax.text(
                mid_x,
                mid_y,
                t["type"],
                ha="center",
                va="center",
                color="white",
                fontsize=8,
                fontweight="bold",
            )

    ax.set_ylim(-1, params["n_cpu"])
    ax.set_yticks(range(params["n_cpu"]))
    ax.set_yticklabels([f"CPU {i}" for i in range(params["n_cpu"])])
    ax.set_xlabel("Time (µs)")
    ax.set_title(f"Transaction Processing Schedule (Makespan: {makespan} µs)")
    ax.grid(True, axis="x", linestyle="--", alpha=0.5)
    ax.legend(handles=legend_patches, loc="upper right")

    plt.tight_layout()
    plt.savefig(filename)
    print(f"Gantt chart saved to: {filename}")


# ==========================================
# 3. SOLVER
# ==========================================
def solve_system(params, dag, log_progress=False, gap=None, abs_gap=None):
    """
    Solves the scheduling problem.
    Returns (makespan, schedule_list, stats_dict) on success.
    Returns None on failure.
    Does NO file I/O.
    """
    model = cp_model.CpModel()

    t_rh = params["delta_rh"]
    t_rb = t_rh + params["delta_rb"]
    t_eh = t_rh + params["delta_eh"]

    # Calculate Horizon
    # LG nodes have no cost, so we must filter them out of the sum
    active_nodes = [d for n, d in dag.nodes(data=True) if d["type"] != "LG"]

    total_verify = sum(d["cost_verify"] for d in active_nodes)
    total_apply = sum(d["cost_apply"] for d in active_nodes)
    total_ops = total_verify + total_apply + params["cost_vote"]

    max_node_delay = (
        max([d["arrival_delay"] for d in active_nodes]) if active_nodes else 0
    )
    max_arrival = max(t_rb, t_eh + max_node_delay)

    horizon = max_arrival + total_ops + 20

    all_intervals = []
    apply_end_vars = {}
    task_metadata = {}

    # Topological sort ensures we process parents before children
    for node_id in nx.topological_sort(dag):
        attrs = dag.nodes[node_id]
        node_type = attrs["type"]

        # LG nodes are state roots; they don't produce tasks.
        if node_type == "LG":
            continue

        cost_v = attrs["cost_verify"]
        cost_a = attrs["cost_apply"]

        if node_type == "RB":
            arrival_time = t_rb + attrs.get("arrival_delay", 0)
        else:
            arrival_time = t_eh + attrs["arrival_delay"]

        # Verify
        v_start = model.NewIntVar(arrival_time, horizon, f"v_s_{node_id}")
        v_end = model.NewIntVar(0, horizon, f"v_e_{node_id}")
        v_interval = model.NewIntervalVar(v_start, cost_v, v_end, f"iv_v_{node_id}")
        all_intervals.append(v_interval)
        task_metadata[f"iv_v_{node_id}"] = {"type": "Ver", "id": node_id}

        # Apply
        a_start = model.NewIntVar(0, horizon, f"a_s_{node_id}")
        a_end = model.NewIntVar(0, horizon, f"a_e_{node_id}")
        a_interval = model.NewIntervalVar(a_start, cost_a, a_end, f"iv_a_{node_id}")
        all_intervals.append(a_interval)
        apply_end_vars[node_id] = a_end
        task_metadata[f"iv_a_{node_id}"] = {"type": "App", "id": node_id}

        model.Add(a_start >= v_end)

        # DAG Dependencies (Parent Apply -> Child Apply)
        for parent in dag.predecessors(node_id):
            parent_type = dag.nodes[parent]["type"]
            # If parent is LG, it is a state root (available at t=0). No constraint needed.
            # If parent is RB/EH, we must wait for its application.
            if parent_type != "LG":
                model.Add(a_start >= apply_end_vars[parent])

    # Vote (Global Task)
    vt_start = model.NewIntVar(0, horizon, "vt_s")
    vt_end = model.NewIntVar(0, horizon, "vt_e")
    vt_interval = model.NewIntervalVar(vt_start, params["cost_vote"], vt_end, "iv_vt")
    all_intervals.append(vt_interval)
    task_metadata["iv_vt"] = {"type": "Vote", "id": "Global"}

    # Vote must wait for all Apply tasks
    for node_id in dag.nodes():
        if dag.nodes[node_id]["type"] != "LG":
            model.Add(vt_start >= apply_end_vars[node_id])

    model.AddCumulative(all_intervals, [1] * len(all_intervals), params["n_cpu"])
    model.Minimize(vt_end)

    solver = cp_model.CpSolver()
    if log_progress:
        solver.parameters.log_search_progress = True

    # Handle environment-specific missing attributes gracefully
    if gap is not None:
        try:
            solver.parameters.relative_gap_tolerance = gap
        except AttributeError:
            print(
                f"Warning: This OR-Tools build does not support 'relative_gap_tolerance'. Ignoring --gap {gap}.",
                file=sys.stderr,
            )

    if abs_gap is not None:
        try:
            solver.parameters.absolute_gap_tolerance = abs_gap
        except AttributeError:
            print(
                f"Warning: This OR-Tools build does not support 'absolute_gap_tolerance'. Ignoring --abs-gap {abs_gap}.",
                file=sys.stderr,
            )

    status = solver.Solve(model)

    # Accept both OPTIMAL and FEASIBLE (if stopped by tolerance or time)
    if status == cp_model.OPTIMAL or status == cp_model.FEASIBLE:
        makespan, schedule = compute_schedule(
            solver, task_metadata, all_intervals, vt_end, params
        )
        stats = calculate_statistics(makespan, schedule, params)
        return makespan, schedule, stats
    else:
        print("No solution found.", file=sys.stderr)
        return None


# ==========================================
# MAIN (CLI)
# ==========================================
def main():
    parser = argparse.ArgumentParser(description="Blockchain Transaction Scheduler")
    parser.add_argument("input_file", nargs="?", help="Input scenario file (JSON/YAML)")

    # Utilities
    parser.add_argument(
        "--generate-dummy", metavar="FILE", help="Generate a dummy input file and exit"
    )

    # Outputs
    parser.add_argument(
        "--out-yaml", metavar="FILE", help="Path to output YAML results"
    )
    parser.add_argument(
        "--out-trace", metavar="FILE", help="Path to output Chrome Trace JSON"
    )
    parser.add_argument(
        "--out-gantt", metavar="FILE", help="Path to output Gantt chart PNG"
    )
    parser.add_argument("--out-csv", metavar="FILE", help="Path to output CSV results")

    # Flags
    parser.add_argument(
        "-v", "--verbose", action="store_true", help="Print schedule to stdout"
    )
    parser.add_argument(
        "--log-solver",
        action="store_true",
        help="Enable internal solver progress logging",
    )
    parser.add_argument(
        "--gap", type=float, help="Relative gap tolerance (e.g. 0.01 for 1%%)"
    )
    parser.add_argument(
        "--abs-gap", type=float, help="Absolute gap tolerance in microseconds"
    )

    args = parser.parse_args()

    if args.generate_dummy:
        generate_dummy_file(args.generate_dummy)
        return

    if not args.input_file:
        parser.print_help()
        sys.exit(0)

    print(f"Reading scenario from {args.input_file}...", file=sys.stderr)
    try:
        params, dag = read_scenario(args.input_file)
    except (FileNotFoundError, ValueError) as e:
        print(f"Error: {e}", file=sys.stderr)
        sys.exit(1)

    print(
        f"Solving for {len(dag.nodes)} transactions on {params['n_cpu']} CPUs...",
        file=sys.stderr,
    )
    result = solve_system(
        params, dag, log_progress=args.log_solver, gap=args.gap, abs_gap=args.abs_gap
    )

    if result:
        makespan, schedule, stats = result
        print_statistics(makespan, stats, file=sys.stderr)

        if args.verbose:
            print_schedule_table(schedule, file=sys.stdout)

        if args.out_yaml:
            write_schedule_yaml(args.out_yaml, makespan, schedule, params, stats)
        if args.out_trace:
            write_chrome_trace(args.out_trace, schedule)
        if args.out_gantt:
            plot_gantt(schedule, makespan, params, args.out_gantt)
        if args.out_csv:
            write_csv(args.out_csv, schedule)
    else:
        sys.exit(1)


if __name__ == "__main__":
    main()
