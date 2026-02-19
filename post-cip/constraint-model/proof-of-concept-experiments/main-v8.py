from ortools.sat.python import cp_model
import networkx as nx
import random


# ==========================================
# 1. SCENARIO GENERATOR
# ==========================================
def generate_scenario():
    """
    Creates a synthetic dataset representing the RB and EH structures.
    """
    # Configuration
    n_rb_tx = 5  # Transactions in the Reference Block
    n_eb_tx = 5  # Transactions in the Endorsement Block

    # Delays and Costs (Arbitrary units, e.g., milliseconds)
    params = {
        "n_cpu": 2,
        "delta_rh": 10,  # Delay for RH arrival
        "delta_rb": 5,  # Delay for RB arrival (relative to RH)
        "delta_eh": 5,  # Delay for EH arrival (relative to RH)
        "cost_verify": 4,  # CPU cost to verify a signature
        "cost_apply": 6,  # CPU cost to apply to ledger
        "cost_vote": 2,  # CPU cost for final vote
    }

    # 1. Build the RB DAG (Roots)
    # For simplicity, let's make a random DAG for RB nodes [0...n_rb_tx-1]
    G = nx.gnp_random_graph(n_rb_tx, 0.4, directed=True)
    dag = nx.DiGraph([(u, v) for (u, v) in G.edges() if u < v])
    for i in range(n_rb_tx):
        dag.add_node(i, type="RB")

    # 2. Build the EH DAG (Extensions)
    # Nodes [n_rb_tx ... n_rb_tx + n_eb_tx - 1]
    # These must extend the RB DAG, so we add edges from RB nodes to EH nodes
    # and edges between EH nodes.

    start_eh = n_rb_tx
    for i in range(n_eb_tx):
        node_id = start_eh + i
        dag.add_node(
            node_id, type="EH", arrival_delay=random.randint(0, 10)
        )  # delta_tb_i

        # Add random dependency on an RB node (Upstream parent)
        parent_rb = random.randint(0, n_rb_tx - 1)
        dag.add_edge(parent_rb, node_id)

        # Add random dependency on a previous EH node (if exists)
        if i > 0:
            parent_eh = start_eh + random.randint(0, i - 1)
            dag.add_edge(parent_eh, node_id)

    return params, dag


# ==========================================
# 2. THE OR-TOOLS SOLVER
# ==========================================
def solve_system(params, dag):
    model = cp_model.CpModel()

    # --- Calculate Absolute Arrival Times ---
    t_rh = params["delta_rh"]
    t_rb = t_rh + params["delta_rb"]
    t_eh = t_rh + params["delta_eh"]

    # Horizon Calculation (Safe upper bound)
    total_ops = (
        len(dag.nodes) * (params["cost_verify"] + params["cost_apply"])
        + params["cost_vote"]
    )
    max_arrival = t_eh + 20  # padding
    horizon = max_arrival + total_ops + 1

    # --- Create Variables ---

    # Stores for interval variables to use in Cumulative constraint
    all_intervals = []

    # Dictionary to store Apply End times for DAG linking
    apply_end_vars = {}

    # Track Task Metadata for visualization
    task_metadata = {}

    for node in dag.nodes(data=True):
        node_id = node[0]
        node_type = node[1]["type"]

        # 1. Determine Data Arrival Time
        if node_type == "RB":
            arrival_time = t_rb
        else:
            # EH Arrival + Individual TB delay
            arrival_time = t_eh + node[1]["arrival_delay"]

        # --- TASK A: VERIFY (Parallelizable immediately upon data arrival) ---
        v_start = model.NewIntVar(arrival_time, horizon, f"v_start_{node_id}")
        v_end = model.NewIntVar(0, horizon, f"v_end_{node_id}")
        v_interval = model.NewIntervalVar(
            v_start, params["cost_verify"], v_end, f"v_task_{node_id}"
        )

        all_intervals.append(v_interval)
        task_metadata[f"v_task_{node_id}"] = {
            "type": "Verify",
            "id": node_id,
            "node_type": node_type,
        }

        # --- TASK B: APPLY (Sequential based on DAG) ---
        a_start = model.NewIntVar(0, horizon, f"a_start_{node_id}")
        a_end = model.NewIntVar(0, horizon, f"a_end_{node_id}")
        a_interval = model.NewIntervalVar(
            a_start, params["cost_apply"], a_end, f"a_task_{node_id}"
        )

        all_intervals.append(a_interval)
        apply_end_vars[node_id] = a_end
        task_metadata[f"a_task_{node_id}"] = {
            "type": "Apply ",
            "id": node_id,
            "node_type": node_type,
        }

        # --- CONSTRAINTS ---

        # 1. Apply must wait for Verify (Same Transaction)
        model.Add(a_start >= v_end)

        # 2. Apply must wait for Parent Apply (DAG Dependency)
        for parent in dag.predecessors(node_id):
            model.Add(a_start >= apply_end_vars[parent])

    # --- TASK C: VOTE (VT) ---
    vt_start = model.NewIntVar(0, horizon, "vt_start")
    vt_end = model.NewIntVar(0, horizon, "vt_end")
    vt_interval = model.NewIntervalVar(vt_start, params["cost_vote"], vt_end, "vt_task")

    all_intervals.append(vt_interval)
    task_metadata["vt_task"] = {"type": "Vote  ", "id": "VT", "node_type": "Global"}

    # VT must wait for ALL Apply tasks to finish
    for node_id in dag.nodes():
        model.Add(vt_start >= apply_end_vars[node_id])

    # --- RESOURCE CONSTRAINT ---
    # Global CPU Limit
    model.AddCumulative(all_intervals, [1] * len(all_intervals), params["n_cpu"])

    # --- OBJECTIVE ---
    model.Minimize(vt_end)

    # --- SOLVE ---
    solver = cp_model.CpSolver()
    status = solver.Solve(model)

    if status == cp_model.OPTIMAL:
        return process_results(solver, task_metadata, all_intervals, vt_end, params)
    else:
        print("No optimal solution found.")
        return None


# ==========================================
# 3. VISUALIZATION & OUTPUT
# ==========================================
def process_results(solver, meta, intervals, makespan_var, params):
    # Extract raw data
    tasks = []
    for iv in intervals:
        name = iv.Name()
        if name:  # Some internal variables might have empty names
            start = solver.Value(iv.StartExpr())
            end = solver.Value(iv.EndExpr())
            info = meta[name]
            tasks.append(
                {
                    "name": name,
                    "start": start,
                    "end": end,
                    "desc": f"{info['type']} {info['node_type']}{info['id']}",
                }
            )

    # Assign CPUs greedily for visualization
    tasks.sort(key=lambda x: x["start"])
    cpu_timeline = [0] * params["n_cpu"]

    for t in tasks:
        assigned = -1
        # Try to fit in first available CPU
        for c in range(params["n_cpu"]):
            if cpu_timeline[c] <= t["start"]:
                assigned = c
                break
        # If greedy fails (edge case), just put on CPU 0
        if assigned == -1:
            assigned = 0

        t["cpu"] = assigned
        cpu_timeline[assigned] = t["end"]

    print(f"\nFinal t1 (Makespan): {solver.Value(makespan_var)}")
    print(
        f"Scenario: {params['n_cpu']} CPUs | Costs: V={params['cost_verify']} A={params['cost_apply']}"
    )
    print("-" * 65)
    print(f"{'CPU':<4} | {'Time':<9} | {'Task Description':<15} | {'Type'}")
    print("-" * 65)

    tasks.sort(key=lambda x: (x["cpu"], x["start"]))

    for t in tasks:
        time_str = f"{t['start']} -> {t['end']}"
        print(f"{t['cpu']:<4} | {time_str:<9} | {t['desc']:<15} | {t['name']}")


# ==========================================
# MAIN EXECUTION
# ==========================================
if __name__ == "__main__":
    p, d = generate_scenario()
    solve_system(p, d)
