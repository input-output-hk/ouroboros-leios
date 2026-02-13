from ortools.sat.python import cp_model
import random

# ==========================================
# 1. SCENARIO GENERATOR
# ==========================================
def generate_data(n_tx=5):
    return {
        'time_rh': 0,
        'time_rb': 5,
        'time_eb': 2,
        'tx_arrivals': {i: random.randint(2, 10) for i in range(n_tx)},
        
        'dur_rb_val': 8,      
        'dur_va1': 3,          
        'dur_va2': 4,          
        'dur_vt': 2,           
        
        'cpu_limit': 2  # Try changing this to 1 or 4 to see the schedule change!
    }

# ==========================================
# 2. HELPER: CPU ALLOCATOR
# ==========================================
def assign_cpus_to_schedule(tasks, cpu_limit):
    """
    Given a list of resolved tasks (start, end, name), assigns them to 
    specific CPU IDs (0..N) using a greedy strategy.
    """
    # 1. Sort tasks by start time
    sorted_tasks = sorted(tasks, key=lambda x: x['start'])
    
    # 2. Track when each CPU becomes free
    # cpu_free_times[0] = 10 means CPU 0 is busy until t=10
    cpu_free_times = [0] * cpu_limit
    
    assigned_schedule = []

    for task in sorted_tasks:
        start, end = task['start'], task['end']
        assigned_cpu = -1
        
        # Find the first CPU that is free at or before the task's start time
        for cpu_id in range(cpu_limit):
            if cpu_free_times[cpu_id] <= start:
                assigned_cpu = cpu_id
                break
        
        # Sanity check: The solver guaranteed this is possible!
        if assigned_cpu == -1:
            # If this hits, the greedy strategy failed (rare edge cases with fragmentation)
            # We just force it onto the CPU that frees up earliest, though this visually implies overlapping
            assigned_cpu = cpu_free_times.index(min(cpu_free_times))

        # Book the CPU
        cpu_free_times[assigned_cpu] = end
        
        # Save result
        task['cpu'] = assigned_cpu
        assigned_schedule.append(task)
        
    return assigned_schedule

# ==========================================
# 3. THE SOLVER
# ==========================================
def solve_schedule(data):
    model = cp_model.CpModel()
    
    # --- Setup Variables (Same as before) ---
    tx_ids = list(data['tx_arrivals'].keys())
    total_work = (data['dur_rb_val'] + len(tx_ids)*(data['dur_va1'] + data['dur_va2']) + data['dur_vt'])
    max_arrival = max(max(data['tx_arrivals'].values()), data['time_rb'])
    horizon = max_arrival + total_work + 50

    # RB Validation
    min_start_rb = max(data['time_rh'], data['time_rb'])
    s_rb = model.NewIntVar(min_start_rb, horizon, 'start_rb')
    e_rb = model.NewIntVar(0, horizon, 'end_rb')
    t_rb = model.NewIntervalVar(s_rb, data['dur_rb_val'], e_rb, 'task_rb')

    # Transactions
    tasks_va1, tasks_va2 = {}, {}
    ends_va1, ends_va2 = {}, {}
    
    for i in tx_ids:
        # VA1
        min_start_va1 = max(data['time_rh'], data['time_eb'], data['tx_arrivals'][i])
        s1 = model.NewIntVar(min_start_va1, horizon, f's1_{i}')
        e1 = model.NewIntVar(0, horizon, f'e1_{i}')
        t1 = model.NewIntervalVar(s1, data['dur_va1'], e1, f't1_{i}')
        tasks_va1[i] = {'iv': t1, 's': s1, 'e': e1}
        ends_va1[i] = e1
        
        # VA2
        s2 = model.NewIntVar(0, horizon, f's2_{i}')
        e2 = model.NewIntVar(0, horizon, f'e2_{i}')
        t2 = model.NewIntervalVar(s2, data['dur_va2'], e2, f't2_{i}')
        tasks_va2[i] = {'iv': t2, 's': s2, 'e': e2}
        ends_va2[i] = e2

    # VT
    s_vt = model.NewIntVar(0, horizon, 's_vt')
    e_vt = model.NewIntVar(0, horizon, 'e_vt')
    t_vt = model.NewIntervalVar(s_vt, data['dur_vt'], e_vt, 't_vt')

    # --- Constraints ---
    for i in tx_ids:
        model.Add(tasks_va2[i]['s'] >= ends_va1[i])  # VA2 after VA1
        model.Add(tasks_va2[i]['s'] >= e_rb)         # VA2 after RB (Gate)
        model.Add(s_vt >= ends_va2[i])               # VT after VA2

    model.Add(s_vt >= e_rb) # VT after RB

    # Resource Constraint
    all_intervals = [t_rb] + [x['iv'] for x in tasks_va1.values()] + [x['iv'] for x in tasks_va2.values()] + [t_vt]
    model.AddCumulative(all_intervals, [1]*len(all_intervals), data['cpu_limit'])

    # Objective
    model.Minimize(e_vt)

    # --- Solve ---
    solver = cp_model.CpSolver()
    status = solver.Solve(model)

    if status == cp_model.OPTIMAL:
        # Collect results into a clean list
        results = []
        
        # RB
        results.append({
            'name': 'RB Val',
            'start': solver.Value(s_rb),
            'end': solver.Value(e_rb),
            'note': 'Gate'
        })
        
        # TXs
        for i in tx_ids:
            # VA1
            results.append({
                'name': f'VA1 Tx{i}',
                'start': solver.Value(tasks_va1[i]['s']),
                'end': solver.Value(tasks_va1[i]['e']),
                'note': f'Arr: {data["tx_arrivals"][i]}'
            })
            # VA2
            results.append({
                'name': f'VA2 Tx{i}',
                'start': solver.Value(tasks_va2[i]['s']),
                'end': solver.Value(tasks_va2[i]['e']),
                'note': 'Post-Gate'
            })
            
        # VT
        results.append({
            'name': 'VT Final',
            'start': solver.Value(s_vt),
            'end': solver.Value(e_vt),
            'note': 'Assembly'
        })

        # --- Assign CPUs and Print ---
        final_schedule = assign_cpus_to_schedule(results, data['cpu_limit'])
        
        print_table(final_schedule, solver.Value(e_vt))
    else:
        print("No solution found.")

def print_table(schedule, makespan):
    print(f"\nFinal Makespan: {makespan}")
    print(f"{'CPU':<4} | {'Task':<10} | {'Start':<6} | {'End':<6} | {'Notes'}")
    print("-" * 50)
    
    # Sort by CPU then Start Time for readability
    schedule.sort(key=lambda x: (x['cpu'], x['start']))
    
    for task in schedule:
        print(f"{task['cpu']:<4} | {task['name']:<10} | {task['start']:<6} | {task['end']:<6} | {task['note']}")

# Run
data_set = generate_data(n_tx=4)
print(f"Scenario: {data_set['cpu_limit']} CPUs. RB arrives at {data_set['time_rb']}")
solve_schedule(data_set)
