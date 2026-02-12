import pulp
import networkx as nx
import random
import shutil

# ==========================================
# 1. SETUP & DATA GENERATION
# ==========================================

def generate_dag(n_tasks, density=0.3, max_duration=5):
    """Generates a random DAG and random durations."""
    G = nx.gnp_random_graph(n_tasks, density, directed=True)
    DAG = nx.DiGraph([(u, v) for (u, v) in G.edges() if u < v])
    
    # Ensure all nodes exist
    for i in range(n_tasks):
        DAG.add_node(i)
        
    durations = {i: random.randint(1, max_duration) for i in range(n_tasks)}
    return DAG, durations

# User Parameters
N_TRANSACTIONS = 8
CPU_LIMIT = 2
MAX_DURATION = 4

# Generate Data
dag, durations = generate_dag(N_TRANSACTIONS, density=0.3, max_duration=MAX_DURATION)
total_cpu_work = sum(durations.values())

# Calculate Horizon (Naive upper bound: sequential execution)
HORIZON = total_cpu_work + 1

print(f"Graph: {N_TRANSACTIONS} txs, {dag.number_of_edges()} dependencies.")
print(f"Total CPU Work needed: {total_cpu_work}")
print(f"Time Horizon: {HORIZON}")

# ==========================================
# 2. MILP FORMULATION (Time-Indexed)
# ==========================================

prob = pulp.LpProblem("DAG_Scheduler_Min_Makespan", pulp.LpMinimize)

# Sets
Tasks = list(range(N_TRANSACTIONS))
Times = list(range(HORIZON))

# --- VARIABLES ---

# x[i][t] = 1 if task i STARTS at time t
x = pulp.LpVariable.dicts("start", (Tasks, Times), cat='Binary')

# C_max: The makespan (Objective)
C_max = pulp.LpVariable("C_max", lowBound=0, upBound=HORIZON, cat='Continuous')

# --- CONSTRAINTS ---

# 1. Each task must start exactly once
for i in Tasks:
    prob += pulp.lpSum([x[i][t] for t in Times]) == 1

# 2. Precedence Constraints (DAG)
# If i -> j, then Start(j) >= Start(i) + Duration(i)
for (i, j) in dag.edges():
    start_i = pulp.lpSum([t * x[i][t] for t in Times])
    start_j = pulp.lpSum([t * x[j][t] for t in Times])
    prob += start_j >= start_i + durations[i]

# 3. Resource Constraints (The "Vertical Cut")
# At any time instant t, the number of ACTIVE tasks must be <= CPU_LIMIT
for t in Times:
    active_tasks = []
    for i in Tasks:
        p_i = durations[i]
        # Task i is active at time t if it started in [t - p_i + 1, t]
        # We sum the start variables in that window
        valid_start_times = range(max(0, t - p_i + 1), t + 1)
        active_tasks.append(pulp.lpSum([x[i][k] for k in valid_start_times]))
    
    prob += pulp.lpSum(active_tasks) <= CPU_LIMIT

# 4. Define Makespan
# C_max >= Start(i) + Duration(i) for all i
for i in Tasks:
    finish_i = pulp.lpSum([t * x[i][t] for t in Times]) + durations[i]
    prob += C_max >= finish_i

# --- OBJECTIVE ---
prob += C_max

# ==========================================
# 3. SOLVE
# ==========================================

# Setup Solver (HiGHS)
highs_path = shutil.which("highs")
solver = pulp.HiGHS_CMD(path=highs_path, msg=False) if highs_path else pulp.PULP_CBC_CMD(msg=False)

print(f"Solving with {solver.__class__.__name__}...")
prob.solve(solver)

# ==========================================
# 4. RESULTS
# ==========================================

print(f"Status: {pulp.LpStatus[prob.status]}")
print(f"Min Wallclock Time (Makespan): {pulp.value(C_max)}")
print(f"Total CPU Time Used: {total_cpu_work}") 
# Note: Total CPU time is constant for a fixed set of tasks, regardless of schedule.

print("\nSchedule:")
print(f"{'TxID':<5} {'Dur':<5} {'Start':<8} {'End':<8} {'Dependencies'}")
print("-" * 50)

# Extract start times
schedule = []
for i in Tasks:
    for t in Times:
        if pulp.value(x[i][t]) > 0.5:
            s_time = t
            break
    schedule.append((i, durations[i], s_time, s_time + durations[i]))

# Sort by start time for readability
schedule.sort(key=lambda k: k[2])

for item in schedule:
    i, d, s, e = item
    preds = list(dag.predecessors(i))
    print(f"{i:<5} {d:<5} {s:<8} {e:<8} {preds}")
