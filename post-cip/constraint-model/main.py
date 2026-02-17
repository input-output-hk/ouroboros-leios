import json
import sys
import networkx as nx
from ortools.sat.python import cp_model

# Try to import PyYAML, handling the case where it's missing
try:
    import yaml
except ImportError:
    yaml = None

# ==========================================
# 1. IO UTILITIES (JSON & YAML)
# ==========================================
def read_scenario(filepath):
    """
    Reads parameters and DAG from a JSON or YAML file.
    Supports .json, .yaml, and .yml extensions.
    
    Expected Schema:
    dag:
      0xHashB:
        type: EH
        arrival_delay: 5
        inputs:
          0: 0xHashA  # Input index -> Parent Hash (Spent Output)
    """
    # Detect format based on extension
    if filepath.lower().endswith(('.yaml', '.yml')):
        if yaml is None:
            print("Error: PyYAML library is missing. Please install it via 'pip install pyyaml'")
            sys.exit(1)
        with open(filepath, 'r') as f:
            data = yaml.safe_load(f)
    else:
        # Default to JSON
        with open(filepath, 'r') as f:
            data = json.load(f)

    params = data['parameters']
    raw_dag = data['dag']
    
    # Build NetworkX DiGraph
    G = nx.DiGraph()
    
    for tx_hash, attrs in raw_dag.items():
        # Add Node
        G.add_node(tx_hash, 
                   type=attrs['type'], 
                   arrival_delay=attrs.get('arrival_delay', 0))
        
        # Add Edges (Inputs -> Dependencies)
        # If current_tx spends parent_tx (parent is input to current), 
        # then current depends on parent. Edge: Parent -> Current.
        inputs = attrs.get('inputs', {})
        
        # Handle list vs dict format for inputs
        if isinstance(inputs, dict):
            parents = inputs.values()
        elif isinstance(inputs, list):
            parents = inputs
        else:
            parents = []
            
        for parent_hash in parents:
            # We add edge FROM parent TO current
            G.add_edge(parent_hash, tx_hash)
            
    return params, G

def generate_dummy_file(filepath):
    """Generates a sample scenario file (JSON or YAML based on extension)."""
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
            # --- RB TRANSACTIONS (Roots) ---
            "0xRB_Root1": {
                "type": "RB",
                "arrival_delay": 0,
                "inputs": []
            },
            "0xRB_Root2": {
                "type": "RB",
                "arrival_delay": 0,
                "inputs": []
            },
            
            # --- EH TRANSACTIONS (Extensions) ---
            "0xEH_Child1": {
                "type": "EH",
                "arrival_delay": 2, 
                "inputs": {
                    "0": "0xRB_Root1",
                    "1": "0xRB_Root2"
                }
            },
            "0xEH_Child2": {
                "type": "EH",
                "arrival_delay": 8,
                "inputs": {
                    "0": "0xRB_Root2"
                }
            },
            "0xEH_GrandChild1": {
                "type": "EH",
                "arrival_delay": 12,
                "inputs": {
                    "0": "0xEH_Child1"
                }
            }
        }
    }
    
    with open(filepath, 'w') as f:
        if filepath.lower().endswith(('.yaml', '.yml')):
            if yaml is None:
                print("Error: PyYAML is missing. Run 'pip install pyyaml'")
                sys.exit(1)
            # sort_keys=False preserves the logical order in Python 3.7+
            yaml.dump(data, f, sort_keys=False, default_flow_style=False)
        else:
            json.dump(data, f, indent=2)
            
    print(f"Generated sample file: {filepath}")

# ==========================================
# 2. THE OR-TOOLS SOLVER
# ==========================================
def solve_system(params, dag):
    model = cp_model.CpModel()
    
    # --- Calculate Absolute Trigger Times ---
    t_rh = params['delta_rh']
    t_rb = t_rh + params['delta_rb']
    t_eh = t_rh + params['delta_eh']
    
    # Horizon Calculation
    count_tx = len(dag.nodes)
    total_ops = count_tx * (params['cost_verify'] + params['cost_apply']) + params['cost_vote']
    # Max explicit delay in the nodes
    max_node_delay = max([d['arrival_delay'] for n, d in dag.nodes(data=True)]) if count_tx > 0 else 0
    max_arrival = max(t_rb, t_eh + max_node_delay)
    
    horizon = max_arrival + total_ops + 20

    # --- Create Variables ---
    all_intervals = []
    apply_end_vars = {}
    task_metadata = {}

    for node_id in dag.nodes():
        attrs = dag.nodes[node_id]
        node_type = attrs['type']
        
        # 1. Determine Data Arrival Time
        if node_type == 'RB':
            # RB nodes arrive in a batch
            arrival_time = t_rb
        else:
            # EH nodes arrive at EH start + their specific delay
            arrival_time = t_eh + attrs['arrival_delay']

        # --- TASK A: VERIFY ---
        v_start = model.NewIntVar(arrival_time, horizon, f'v_s_{node_id}')
        v_end = model.NewIntVar(0, horizon, f'v_e_{node_id}')
        v_interval = model.NewIntervalVar(v_start, params['cost_verify'], v_end, f'iv_v_{node_id}')
        
        all_intervals.append(v_interval)
        task_metadata[f'iv_v_{node_id}'] = {'type': 'Ver', 'id': node_id, 'node_type': node_type}

        # --- TASK B: APPLY ---
        a_start = model.NewIntVar(0, horizon, f'a_s_{node_id}')
        a_end = model.NewIntVar(0, horizon, f'a_e_{node_id}')
        a_interval = model.NewIntervalVar(a_start, params['cost_apply'], a_end, f'iv_a_{node_id}')
        
        all_intervals.append(a_interval)
        apply_end_vars[node_id] = a_end
        task_metadata[f'iv_a_{node_id}'] = {'type': 'App', 'id': node_id, 'node_type': node_type}

        # --- CONSTRAINTS ---
        # 1. Intra-Tx Dependency: Apply after Verify
        model.Add(a_start >= v_end)
        
        # 2. DAG Dependency: Apply after Parent Apply
        # Note: NetworkX predecessors correspond to 'inputs' in UTXO logic
        # If A -> B (A outputs to B), B depends on A.
        for parent in dag.predecessors(node_id):
            model.Add(a_start >= apply_end_vars[parent])

    # --- TASK C: VOTE ---
    vt_start = model.NewIntVar(0, horizon, 'vt_s')
    vt_end = model.NewIntVar(0, horizon, 'vt_e')
    vt_interval = model.NewIntervalVar(vt_start, params['cost_vote'], vt_end, 'iv_vt')
    
    all_intervals.append(vt_interval)
    task_metadata['iv_vt'] = {'type': 'Vote', 'id': 'Global', 'node_type': 'VT'}

    # VT after ALL Applies
    for node_id in dag.nodes():
        model.Add(vt_start >= apply_end_vars[node_id])

    # --- RESOURCE CONSTRAINT ---
    model.AddCumulative(all_intervals, [1] * len(all_intervals), params['n_cpu'])

    # --- OBJECTIVE ---
    model.Minimize(vt_end)

    # --- SOLVE ---
    solver = cp_model.CpSolver()
    status = solver.Solve(model)

    if status == cp_model.OPTIMAL:
        process_results(solver, task_metadata, all_intervals, vt_end, params)
    else:
        print("No optimal solution found.")

# ==========================================
# 3. VISUALIZATION
# ==========================================
def process_results(solver, meta, intervals, makespan_var, params):
    tasks = []
    for iv in intervals:
        name = iv.Name()
        if name in meta:
            start = solver.Value(iv.StartExpr())
            end = solver.Value(iv.EndExpr())
            info = meta[name]
            tasks.append({
                'start': start, 'end': end,
                'desc': f"{info['type']} {info['id']}",
                'raw_id': info['id']
            })
            
    # Greedy CPU Assignment for Visualization
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

    print(f"\nFinal t1 (Makespan): {solver.Value(makespan_var)}")
    print("-" * 75)
    print(f"{'CPU':<4} | {'Time':<12} | {'Task'}")
    print("-" * 75)
    
    tasks.sort(key=lambda x: (x['cpu'], x['start']))
    for t in tasks:
        time_str = f"{t['start']} -> {t['end']}"
        print(f"{t['cpu']:<4} | {time_str:<12} | {t['desc']}")

# ==========================================
# MAIN
# ==========================================
if __name__ == "__main__":
    # Now defaults to generating and reading a YAML file
    yaml_path = "scenario.yaml"
    
    # 1. Create dummy file if needed
    generate_dummy_file(yaml_path)
    
    # 2. Read
    print(f"Reading scenario from {yaml_path}...")
    params, dag = read_scenario(yaml_path)
    
    # 3. Solve
    print(f"Solving for {len(dag.nodes)} transactions on {params['n_cpu']} CPUs...")
    solve_system(params, dag)
