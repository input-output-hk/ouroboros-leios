import json
import sys
import csv  # Added csv module
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
    
    for tx_hash, attrs in raw_dag.items():
        G.add_node(tx_hash, 
                   type=attrs['type'], 
                   arrival_delay=attrs.get('arrival_delay', 0))
        
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
            "delta_rh": 10,
            "delta_rb": 5,
            "delta_eh": 5,
            "cost_verify": 4,
            "cost_apply": 6,
            "cost_vote": 2
        },
        "dag": {
            "0xRB_Root1": {"type": "RB", "arrival_delay": 0, "inputs": []},
            "0xRB_Root2": {"type": "RB", "arrival_delay": 0, "inputs": []},
            "0xEH_Child1": {"type": "EH", "arrival_delay": 2, "inputs": {"0": "0xRB_Root1", "1": "0xRB_Root2"}},
            "0xEH_Child2": {"type": "EH", "arrival_delay": 8, "inputs": {"0": "0xRB_Root2"}},
            "0xEH_GrandChild1": {"type": "EH", "arrival_delay": 12, "inputs": {"0": "0xEH_Child1"}}
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
# 2. OUTPUT & VISUALIZATION
# ==========================================
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

def print_schedule(makespan, tasks):
    print(f"\nFinal t1 (Makespan): {makespan}")
    print("-" * 75)
    print(f"{'CPU':<4} | {'Time':<12} | {'Task'}")
    print("-" * 75)
    tasks_sorted = sorted(tasks, key=lambda x: (x['cpu'], x['start']))
    for t in tasks_sorted:
        time_str = f"{t['start']} -> {t['end']}"
        print(f"{t['cpu']:<4} | {time_str:<12} | {t['desc']}")

def write_schedule_yaml(filepath, makespan, tasks, params):
    if yaml is None: return
    output_data = {
        "parameters": params,
        "results": {"makespan": makespan, "schedule": []}
    }
    tasks_sorted = sorted(tasks, key=lambda x: x['start'])
    for t in tasks_sorted:
        output_data["results"]["schedule"].append({
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
    """
    Writes the schedule to Chrome Tracing JSON format.
    Load this file in ui.perfetto.dev or chrome://tracing
    """
    trace_events = []
    
    for t in tasks:
        # Chrome trace uses microseconds, we multiply by 1000 for visibility
        scale = 1000
        
        # Color ID mappings (cname is optional, but cat helps)
        # Categories: Verify, Apply, Vote
        
        event = {
            "name": t['desc'],
            "cat": t['type'],
            "ph": "X",          # Phase: Complete Event
            "ts": t['start'] * scale,
            "dur": (t['end'] - t['start']) * scale,
            "pid": 1,           # Process ID (The blockchain node)
            "tid": t['cpu'],    # Thread ID (The CPU core)
            "args": {
                "raw_id": str(t['raw_id'])
            }
        }
        trace_events.append(event)
        
    wrapper = {"traceEvents": trace_events}
    
    with open(filepath, 'w') as f:
        json.dump(wrapper, f)
    
    print(f"Chrome Trace written to: {filepath}")
    print("  -> Open https://ui.perfetto.dev/ and load this file to visualize.")

def write_csv(filepath, tasks):
    """
    Writes the schedule to CSV format. 
    Compatible with Grafana/Excel/Pandas.
    """
    with open(filepath, 'w', newline='') as f:
        writer = csv.writer(f)
        writer.writerow(['TaskID', 'Type', 'Description', 'CPU', 'Start', 'End', 'Duration'])
        for t in tasks:
            writer.writerow([
                t['raw_id'], t['type'], t['desc'], t['cpu'], t['start'], t['end'], t['end'] - t['start']
            ])
    print(f"CSV results written to: {filepath}")

def plot_gantt(tasks, makespan, params, filename="gantt.png"):
    """Generates a static Gantt chart using Matplotlib."""
    if not MATPLOTLIB_AVAILABLE:
        print("Warning: Matplotlib not installed. Skipping Gantt chart.")
        return

    fig, ax = plt.subplots(figsize=(12, 6))
    
    # Colors for different task types
    colors = {'Ver': 'tab:blue', 'App': 'tab:orange', 'Vote': 'tab:green'}
    legend_patches = []
    for k, v in colors.items():
        legend_patches.append(mpatches.Patch(color=v, label=k))

    # Y-axis is CPU ID
    # X-axis is Time
    
    for t in tasks:
        c = colors.get(t['type'], 'gray')
        # (start_time, cpu_index, duration, height)
        # We plot bars horizontally
        # y = t['cpu'], width = duration, left = start
        ax.broken_barh([(t['start'], t['end'] - t['start'])], 
                       (t['cpu'] - 0.4, 0.8), 
                       facecolors=c, edgecolors='white')
        
        # Optional: Add text label if duration is long enough
        if (t['end'] - t['start']) > 2:
            mid_x = t['start'] + (t['end'] - t['start'])/2
            mid_y = t['cpu']
            ax.text(mid_x, mid_y, t['type'], ha='center', va='center', 
                    color='white', fontsize=8, fontweight='bold')

    ax.set_ylim(-1, params['n_cpu'])
    ax.set_yticks(range(params['n_cpu']))
    ax.set_yticklabels([f"CPU {i}" for i in range(params['n_cpu'])])
    ax.set_xlabel("Time (ticks)")
    ax.set_title(f"Transaction Processing Schedule (Makespan: {makespan})")
    ax.grid(True, axis='x', linestyle='--', alpha=0.5)
    ax.legend(handles=legend_patches, loc='upper right')
    
    plt.tight_layout()
    plt.savefig(filename)
    print(f"Gantt chart saved to: {filename}")

# ==========================================
# 3. SOLVER
# ==========================================
def solve_system(params, dag, output_yaml_path=None, trace_path=None, gantt_path=None, csv_path=None):
    model = cp_model.CpModel()
    
    t_rh = params['delta_rh']
    t_rb = t_rh + params['delta_rb']
    t_eh = t_rh + params['delta_eh']
    
    count_tx = len(dag.nodes)
    total_ops = count_tx * (params['cost_verify'] + params['cost_apply']) + params['cost_vote']
    max_node_delay = max([d['arrival_delay'] for n, d in dag.nodes(data=True)]) if count_tx > 0 else 0
    max_arrival = max(t_rb, t_eh + max_node_delay)
    
    horizon = max_arrival + total_ops + 20

    all_intervals = []
    apply_end_vars = {}
    task_metadata = {}

    for node_id in dag.nodes():
        attrs = dag.nodes[node_id]
        node_type = attrs['type']
        
        if node_type == 'RB':
            arrival_time = t_rb
        else:
            arrival_time = t_eh + attrs['arrival_delay']

        # Verify
        v_start = model.NewIntVar(arrival_time, horizon, f'v_s_{node_id}')
        v_end = model.NewIntVar(0, horizon, f'v_e_{node_id}')
        v_interval = model.NewIntervalVar(v_start, params['cost_verify'], v_end, f'iv_v_{node_id}')
        all_intervals.append(v_interval)
        task_metadata[f'iv_v_{node_id}'] = {'type': 'Ver', 'id': node_id}

        # Apply
        a_start = model.NewIntVar(0, horizon, f'a_s_{node_id}')
        a_end = model.NewIntVar(0, horizon, f'a_e_{node_id}')
        a_interval = model.NewIntervalVar(a_start, params['cost_apply'], a_end, f'iv_a_{node_id}')
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
        print_schedule(makespan, schedule)
        
        if output_yaml_path:
            write_schedule_yaml(output_yaml_path, makespan, schedule, params)
        if trace_path:
            write_chrome_trace(trace_path, schedule)
        if gantt_path:
            plot_gantt(schedule, makespan, params, gantt_path)
        if csv_path:
            write_csv(csv_path, schedule)
    else:
        print("No optimal solution found.")

# ==========================================
# MAIN
# ==========================================
if __name__ == "__main__":
    input_yaml = "scenario.yaml"
    output_yaml = "results.yaml"
    trace_json = "trace.json"
    gantt_png = "schedule.png"
    results_csv = "schedule.csv"
    
    # 1. Create dummy file if needed
    generate_dummy_file(input_yaml)
    
    # 2. Read
    print(f"Reading scenario from {input_yaml}...")
    params, dag = read_scenario(input_yaml)
    
    # 3. Solve
    print(f"Solving for {len(dag.nodes)} transactions on {params['n_cpu']} CPUs...")
    solve_system(params, dag, output_yaml, trace_json, gantt_png, results_csv)
