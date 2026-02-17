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
    if filepath.lower().endswith(('.yaml', '.yml')):
        if yaml is None:
            print("Error: PyYAML library is missing. Please install it via 'pip install pyyaml'")
            sys.exit(1)
        with open(filepath, 'r') as f:
            data = yaml.safe_load(f)
    else:
        with open(filepath, 'r') as f:
            data = json.load(f)

    params = data['parameters']
    raw_dag = data['dag']
    
    G = nx.DiGraph()
    
    # Global defaults for fallback
    default_verify = params.get('cost_verify', 0)
    default_apply = params.get('cost_apply', 0)
    
    for tx_hash, attrs in raw_dag.items():
        G.add_node(tx_hash, 
                   type=attrs['type'], 
                   arrival_delay=attrs.get('arrival_delay', 0),
                   # Read per-transaction costs, fall back to global default
                   cost_verify=attrs.get('cost_verify', default_verify),
                   cost_apply=attrs.get('cost_apply', default_apply))
        
        inputs = attrs.get('inputs', {})
        if isinstance(inputs, dict):
            parents = inputs.values()
        elif isinstance(inputs, list):
            parents = inputs
        else:
            parents = []
            
        for parent_hash in parents:
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
            # Global defaults (optional, used if not on node)
            "cost_verify": 4000,
            "cost_apply": 6000,
            "cost_vote": 2000
        },
        "dag": {
            "0xRB_Root1": {
                "type": "RB", 
                "arrival_delay": 1230, 
                "inputs": [],
                "cost_verify": 3500, # Specific cost
                "cost_apply": 5500
            },
            "0xRB_Root2": {
                "type": "RB", 
                "arrival_delay": 4710, 
                "inputs": [] # Uses defaults
            },
            "0xEH_Child1": {
                "type": "EH", 
                "arrival_delay": 2000, 
                "inputs": {"0": "0xRB_Root1", "1": "0xRB_Root2"},
                "cost_verify": 4200,
                "cost_apply": 6100
            },
            "0xEH_Child2": {
                "type": "EH", 
                "arrival_delay": 8000, 
                "inputs": {"0": "0xRB_Root2"}
            },
            "0xEH_GrandChild1": {
                "type": "EH", 
                "arrival_delay": 12000, 
                "inputs": {"0": "0xEH_Child1"}
            }
        }
    }
    
    with open(filepath, 'w') as f:
        if filepath.lower().endswith(('.yaml', '.yml')):
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
    """
    Computes detailed performance metrics.
    """
    n_cpu = params['n_cpu']
    total_capacity = makespan * n_cpu
    total_work = sum(t['end'] - t['start'] for t in tasks)
    
    stats = {
        "makespan": makespan,
        "n_cpu": n_cpu,
        "total_capacity_cycles": total_capacity,
        "total_work_cycles": total_work,
        "cpu_utilization": total_work / total_capacity if total_capacity > 0 else 0.0,
    }
    
    # Phase Analysis
    phases = ['Ver', 'App', 'Vote']
    phase_stats = {}
    
    for p in phases:
        p_tasks = [t for t in tasks if t['type'] == p]
        if not p_tasks:
            phase_stats[p] = {
                "work_cycles": 0, 
                "fraction_of_total_work": 0.0, 
                "avg_parallelism": 0.0
            }
            continue
            
        work = sum(t['end'] - t['start'] for t in p_tasks)
        start_t = min(t['start'] for t in p_tasks)
        end_t = max(t['end'] for t in p_tasks)
        wallclock_dur = end_t - start_t
        
        phase_stats[p] = {
            "work_cycles": work,
            "fraction_of_total_work": work / total_work if total_work > 0 else 0.0,
            # Parallelism = Total CPU Time / Wallclock Time
            "avg_parallelism": work / wallclock_dur if wallclock_dur > 0 else 0.0,
            "phase_wallclock_duration": wallclock_dur
        }
    stats["phases"] = phase_stats
    
    # Wallclock Idle Time
    sorted_tasks = sorted(tasks, key=lambda x: x['start'])
    active_ranges = []
    
    if sorted_tasks:
        curr_start, curr_end = sorted_tasks[0]['start'], sorted_tasks[0]['end']
        for t in sorted_tasks[1:]:
            if t['start'] < curr_end:
                curr_end = max(curr_end, t['end'])
            else:
                active_ranges.append((curr_start, curr_end))
                curr_start, curr_end = t['start'], t['end']
        active_ranges.append((curr_start, curr_end))
    
    total_active_wallclock = sum(end - start for start, end in active_ranges)
    wallclock_idle = makespan - total_active_wallclock
    
    stats["wallclock_idle"] = wallclock_idle
    stats["fraction_wallclock_idle"] = wallclock_idle / makespan if makespan > 0 else 0.0
    
    return stats

def compute_schedule(solver, meta, intervals, makespan_var, params):
    tasks = []
    for iv in intervals:
        name = iv.Name()
        if name in meta:
            start = solver.Value(iv.StartExpr())
            end = solver.Value(iv.EndExpr())
            info = meta[name]
            tasks.append({
                'start': start, 
                'end': end,
                'desc': f"{info['type']} {info['id']}",
                'type': info['type'],
                'raw_id': info['id']
            })
            
    # Greedy CPU Assignment
    tasks.sort(key=lambda x: x['start'])
    cpu_timeline = [0] * params['n_cpu']
    
    for t in tasks:
        assigned = 0
        for c in range(params['n_cpu']):
            if cpu_timeline[c] <= t['start']:
                assigned = c
                break
        t['cpu'] = assigned
        cpu_timeline[assigned] = t['end']
        
    return solver.Value(makespan_var), tasks

def print_schedule_table(tasks, file=sys.stdout):
    """Prints the detailed schedule table."""
    print(f"\nSCHEDULE TABLE", file=file)
    print("-" * 75, file=file)
    print(f"{'CPU':<4} | {'Time (µs)':<15} | {'Task'}", file=file)
    print("-" * 75, file=file)
    tasks_sorted = sorted(tasks, key=lambda x: (x['cpu'], x['start']))
    for t in tasks_sorted:
        time_str = f"{t['start']} -> {t['end']}"
        print(f"{t['cpu']:<4} | {time_str:<15} | {t['desc']}", file=file)

def print_statistics(makespan, stats, file=sys.stderr):
    """Prints the summary statistics."""
    print(f"\nFinal t1 (Makespan): {makespan} µs", file=file)
    print("="*40, file=file)
    print("PERFORMANCE STATISTICS", file=file)
    print("="*40, file=file)
    print(f"CPU Utilization:       {stats['cpu_utilization']:.1%}", file=file)
    print(f"Wallclock Idle:        {stats['fraction_wallclock_idle']:.1%} ({stats['wallclock_idle']} µs)", file=file)
    print("-" * 40, file=file)
    print(f"{'Phase':<6} | {'Work %':<8} | {'Parallelism':<11}", file=file)
    print("-" * 40, file=file)
    for p, data in stats['phases'].items():
        print(f"{p:<6} | {data['fraction_of_total_work']:<8.1%} | {data['avg_parallelism']:<11.2f}", file=file)
    print("="*40, file=file)

def write_schedule_yaml(filepath, makespan, tasks, params, stats):
    if yaml is None: return
    output_data = {
        "parameters": params,
        "statistics": stats,
        "schedule": []
    }
    tasks_sorted = sorted(tasks, key=lambda x: x['start'])
    for t in tasks_sorted:
        output_data["schedule"].append({
            "id": t['raw_id'],
            "type": t['type'],
            "cpu": t['cpu'],
            "start": t['start'],
            "end": t['end'],
            "duration": t['end'] - t['start']
        })
    with open(filepath, 'w') as f:
        yaml.dump(output_data, f, sort_keys=False, default_flow_style=False)
    print(f"YAML results written to: {filepath}")

def write_chrome_trace(filepath, tasks):
    trace_events = []
    for t in tasks:
        # Scale = 1 because units are already microseconds
        scale = 1
        event = {
            "name": t['desc'],
            "cat": t['type'],
            "ph": "X",
            "ts": t['start'] * scale,
            "dur": (t['end'] - t['start']) * scale,
            "pid": 1,
            "tid": t['cpu'],
            "args": {"raw_id": str(t['raw_id'])}
        }
        trace_events.append(event)
        
    wrapper = {"traceEvents": trace_events}
    with open(filepath, 'w') as f:
        json.dump(wrapper, f)
    print(f"Chrome Trace written to: {filepath}")

def write_csv(filepath, tasks):
    with open(filepath, 'w', newline='') as f:
        writer = csv.writer(f)
        writer.writerow(['TaskID', 'Type', 'Description', 'CPU', 'Start', 'End', 'Duration'])
        for t in tasks:
            writer.writerow([
                t['raw_id'], t['type'], t['desc'], t['cpu'], t['start'], t['end'], t['end'] - t['start']
            ])
    print(f"CSV results written to: {filepath}")

def plot_gantt(tasks, makespan, params, filename="gantt.png"):
    if not MATPLOTLIB_AVAILABLE:
        print("Warning: Matplotlib not installed. Skipping Gantt chart.")
        return

    fig, ax = plt.subplots(figsize=(12, 6))
    colors = {'Ver': 'tab:blue', 'App': 'tab:orange', 'Vote': 'tab:green'}
    legend_patches = [mpatches.Patch(color=v, label=k) for k,v in colors.items()]

    for t in tasks:
        c = colors.get(t['type'], 'gray')
        ax.broken_barh([(t['start'], t['end'] - t['start'])], 
                       (t['cpu'] - 0.4, 0.8), 
                       facecolors=c, edgecolors='white')
        
        if (t['end'] - t['start']) > 2:
            mid_x = t['start'] + (t['end'] - t['start'])/2
            mid_y = t['cpu']
            ax.text(mid_x, mid_y, t['type'], ha='center', va='center', 
                    color='white', fontsize=8, fontweight='bold')

    ax.set_ylim(-1, params['n_cpu'])
    ax.set_yticks(range(params['n_cpu']))
    ax.set_yticklabels([f"CPU {i}" for i in range(params['n_cpu'])])
    ax.set_xlabel("Time (µs)")
    ax.set_title(f"Transaction Processing Schedule (Makespan: {makespan} µs)")
    ax.grid(True, axis='x', linestyle='--', alpha=0.5)
    ax.legend(handles=legend_patches, loc='upper right')
    
    plt.tight_layout()
    plt.savefig(filename)
    print(f"Gantt chart saved to: {filename}")

# ==========================================
# 3. SOLVER
# ==========================================
def solve_system(params, dag):
    """
    Solves the scheduling problem.
    Returns (makespan, schedule_list, stats_dict) on success.
    Returns None on failure.
    Does NO file I/O.
    """
    model = cp_model.CpModel()
    
    t_rh = params['delta_rh']
    t_rb = t_rh + params['delta_rb']
    t_eh = t_rh + params['delta_eh']
    
    # Calculate Horizon
    # We now must sum up individual costs since they vary
    total_verify = sum(d['cost_verify'] for n, d in dag.nodes(data=True))
    total_apply = sum(d['cost_apply'] for n, d in dag.nodes(data=True))
    total_ops = total_verify + total_apply + params['cost_vote']
    
    count_tx = len(dag.nodes)
    max_node_delay = max([d['arrival_delay'] for n, d in dag.nodes(data=True)]) if count_tx > 0 else 0
    max_arrival = max(t_rb, t_eh + max_node_delay)
    
    horizon = max_arrival + total_ops + 20

    all_intervals = []
    apply_end_vars = {}
    task_metadata = {}

    for node_id in dag.nodes():
        attrs = dag.nodes[node_id]
        node_type = attrs['type']
        
        # Get specific costs (already populated by read_scenario)
        cost_v = attrs['cost_verify']
        cost_a = attrs['cost_apply']
        
        if node_type == 'RB':
            arrival_time = t_rb
        else:
            arrival_time = t_eh + attrs['arrival_delay']

        # Verify
        v_start = model.NewIntVar(arrival_time, horizon, f'v_s_{node_id}')
        v_end = model.NewIntVar(0, horizon, f'v_e_{node_id}')
        v_interval = model.NewIntervalVar(v_start, cost_v, v_end, f'iv_v_{node_id}')
        all_intervals.append(v_interval)
        task_metadata[f'iv_v_{node_id}'] = {'type': 'Ver', 'id': node_id}

        # Apply
        a_start = model.NewIntVar(0, horizon, f'a_s_{node_id}')
        a_end = model.NewIntVar(0, horizon, f'a_e_{node_id}')
        a_interval = model.NewIntervalVar(a_start, cost_a, a_end, f'iv_a_{node_id}')
        all_intervals.append(a_interval)
        apply_end_vars[node_id] = a_end
        task_metadata[f'iv_a_{node_id}'] = {'type': 'App', 'id': node_id}

        model.Add(a_start >= v_end)
        for parent in dag.predecessors(node_id):
            model.Add(a_start >= apply_end_vars[parent])

    # Vote
    vt_start = model.NewIntVar(0, horizon, 'vt_s')
    vt_end = model.NewIntVar(0, horizon, 'vt_e')
    vt_interval = model.NewIntervalVar(vt_start, params['cost_vote'], vt_end, 'iv_vt')
    all_intervals.append(vt_interval)
    task_metadata['iv_vt'] = {'type': 'Vote', 'id': 'Global'}

    for node_id in dag.nodes():
        model.Add(vt_start >= apply_end_vars[node_id])

    model.AddCumulative(all_intervals, [1] * len(all_intervals), params['n_cpu'])
    model.Minimize(vt_end)

    solver = cp_model.CpSolver()
    status = solver.Solve(model)

    if status == cp_model.OPTIMAL:
        makespan, schedule = compute_schedule(solver, task_metadata, all_intervals, vt_end, params)
        stats = calculate_statistics(makespan, schedule, params)
        return makespan, schedule, stats
    else:
        print("No optimal solution found.", file=sys.stderr)
        return None

# ==========================================
# MAIN (CLI)
# ==========================================
def main():
    parser = argparse.ArgumentParser(description="Blockchain Transaction Scheduler")
    parser.add_argument("input_file", nargs='?', help="Input scenario file (JSON/YAML)")
    
    # Utilities
    parser.add_argument("--generate-dummy", metavar="FILE", help="Generate a dummy input file and exit")
    
    # Outputs
    parser.add_argument("--out-yaml", metavar="FILE", help="Path to output YAML results")
    parser.add_argument("--out-trace", metavar="FILE", help="Path to output Chrome Trace JSON")
    parser.add_argument("--out-gantt", metavar="FILE", help="Path to output Gantt chart PNG")
    parser.add_argument("--out-csv", metavar="FILE", help="Path to output CSV results")
    
    # Flags
    parser.add_argument("-v", "--verbose", action="store_true", help="Print schedule to stdout")
    
    args = parser.parse_args()
    
    # Mode 1: Generator
    if args.generate_dummy:
        generate_dummy_file(args.generate_dummy)
        return

    # Mode 2: Solver
    if not args.input_file:
        parser.print_help()
        sys.exit(0)

    # 1. Read
    print(f"Reading scenario from {args.input_file}...", file=sys.stderr)
    try:
        params, dag = read_scenario(args.input_file)
    except FileNotFoundError:
        print(f"Error: File '{args.input_file}' not found.", file=sys.stderr)
        sys.exit(1)
    
    # 2. Solve
    print(f"Solving for {len(dag.nodes)} transactions on {params['n_cpu']} CPUs...", file=sys.stderr)
    result = solve_system(params, dag)
    
    if result:
        makespan, schedule, stats = result
        
        # 3. Output
        # Statistics always go to stderr
        print_statistics(makespan, stats, file=sys.stderr)
        
        # Verbose schedule always goes to stdout
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
