from ortools.sat.python import cp_model
import random

# ==========================================
# 1. SCENARIO GENERATOR
# ==========================================
def generate_data(n_tx=5):
    """Generates random arrival times and durations."""
    return {
        # Arrivals (The "Wait" constraints)
        'time_rh': 0,          # The workflow start trigger
        'time_rb': 5,          # RB arrives a bit later
        'time_eb': 2,          # EB arrives early
        'tx_arrivals': {i: random.randint(2, 15) for i in range(n_tx)},
        
        # Durations (Processing cost)
        'dur_rb_val': 10,      # Validating RB is slow
        'dur_va1': 3,          # VA1 is fast
        'dur_va2': 4,          # VA2 is moderate
        'dur_vt': 2,           # Final check is fast
        
        # Resources
        'cpu_limit': 2
    }

# ==========================================
# 2. THE SOLVER
# ==========================================
def solve_schedule(data):
    model = cp_model.CpModel()
    
    # --- Unpack Data ---
    tx_ids = list(data['tx_arrivals'].keys())
    # Horizon: A safe upper bound (sum of all durations + max arrival)
    total_work = (data['dur_rb_val'] + 
                  len(tx_ids) * (data['dur_va1'] + data['dur_va2']) + 
                  data['dur_vt'])
    max_arrival = max(max(data['tx_arrivals'].values()), data['time_rb'])
    horizon = max_arrival + total_work + 10

    # --- Create Variables (Intervals) ---
    
    # 1. RB Validation
    # Must wait for RH and RB arrivals
    min_start_rb = max(data['time_rh'], data['time_rb'])
    
    start_rb = model.NewIntVar(min_start_rb, horizon, 'start_rb')
    end_rb = model.NewIntVar(0, horizon, 'end_rb')
    # Use fixed duration
    task_rb = model.NewIntervalVar(start_rb, data['dur_rb_val'], end_rb, 'task_rb')

    # 2. Transaction Validation (VA1 and VA2)
    tasks_va1 = {} # Map tx_id -> interval
    tasks_va2 = {}
    ends_va1 = {}  # To link VA1 -> VA2
    ends_va2 = {}  # To link VA2 -> VT
    
    for i in tx_ids:
        # --- VA1 ---
        # Must wait for RH, EB, and the specific TX arrival
        min_start_va1 = max(data['time_rh'], data['time_eb'], data['tx_arrivals'][i])
        
        s1 = model.NewIntVar(min_start_va1, horizon, f'start_va1_{i}')
        e1 = model.NewIntVar(0, horizon, f'end_va1_{i}')
        t1 = model.NewIntervalVar(s1, data['dur_va1'], e1, f'task_va1_{i}')
        
        tasks_va1[i] = t1
        ends_va1[i] = e1
        
        # --- VA2 ---
        # Start time is unconstrained by arrivals, but constrained by dependencies
        s2 = model.NewIntVar(0, horizon, f'start_va2_{i}')
        e2 = model.NewIntVar(0, horizon, f'end_va2_{i}')
        t2 = model.NewIntervalVar(s2, data['dur_va2'], e2, f'task_va2_{i}')
        
        tasks_va2[i] = t2
        ends_va2[i] = e2

    # 3. Final VT
    start_vt = model.NewIntVar(0, horizon, 'start_vt')
    end_vt = model.NewIntVar(0, horizon, 'end_vt')
    task_vt = model.NewIntervalVar(start_vt, data['dur_vt'], end_vt, 'task_vt')

    # --- Add Constraints ---

    # Dependency A: VA2 must wait for VA1 (Per transaction)
    for i in tx_ids:
        model.Add(tasks_va2[i].StartExpr() >= ends_va1[i])
        
    # Dependency B: VA2 must wait for RB Validation (The "Gate")
    for i in tx_ids:
        model.Add(tasks_va2[i].StartExpr() >= end_rb)

    # Dependency C: VT must wait for EVERYTHING
    # (Waiting for all VA2s implies waiting for VA1s and RB)
    model.Add(start_vt >= end_rb) 
    for i in tx_ids:
        model.Add(start_vt >= ends_va2[i])

    # Resource Constraints (CPUs)
    # Collect all intervals that consume CPU
    all_intervals = [task_rb] + list(tasks_va1.values()) + list(tasks_va2.values()) + [task_vt]
    all_demands = [1] * len(all_intervals) # Assume each task takes 1 CPU
    
    model.AddCumulative(all_intervals, all_demands, data['cpu_limit'])

    # --- Objective ---
    model.Minimize(end_vt)

    # --- Solve ---
    solver = cp_model.CpSolver()
    status = solver.Solve(model)

    if status == cp_model.OPTIMAL:
        print_solution(solver, data, start_rb, end_rb, tasks_va1, tasks_va2, start_vt, end_vt)
    else:
        print("No optimal solution found.")

def print_solution(solver, data, s_rb, e_rb, t_va1, t_va2, s_vt, e_vt):
    print(f"Makespan: {solver.Value(e_vt)}")
    print("-" * 60)
    print(f"{'Task':<10} | {'Arrival':<8} | {'Start':<6} | {'End':<6} | {'Notes'}")
    print("-" * 60)
    
    # RB Info
    rb_arr = data['time_rb']
    print(f"{'RB Val':<10} | {rb_arr:<8} | {solver.Value(s_rb):<6} | {solver.Value(e_rb):<6} | Main Gate")
    
    # TX Info
    tx_ids = sorted(data['tx_arrivals'].keys())
    for i in tx_ids:
        arr = data['tx_arrivals'][i]
        
        # VA1
        s1 = solver.Value(t_va1[i].StartExpr())
        e1 = solver.Value(t_va1[i].EndExpr())
        print(f"{f'VA1 Tx{i}':<10} | {arr:<8} | {s1:<6} | {e1:<6} | Waits for EB+Tx")
        
        # VA2
        s2 = solver.Value(t_va2[i].StartExpr())
        e2 = solver.Value(t_va2[i].EndExpr())
        print(f"{f'VA2 Tx{i}':<10} | {'-':<8} | {s2:<6} | {e2:<6} | Waits for VA1+RB")

    # VT Info
    print(f"{'VT':<10} | {'-':<8} | {solver.Value(s_vt):<6} | {solver.Value(e_vt):<6} | Final Step")

# Run
data_set = generate_data(n_tx=3)
print(f"Scenario: RB Arrives at {data_set['time_rb']}, EB at {data_set['time_eb']}")
solve_schedule(data_set)
