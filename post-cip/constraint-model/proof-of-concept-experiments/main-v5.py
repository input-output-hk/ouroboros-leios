from ortools.sat.python import cp_model

# 1. Setup Data (Same as before)
tasks_data = [
    {'id': 0, 'duration': 3, 'cpu': 1, 'deps': []},
    {'id': 1, 'duration': 2, 'cpu': 1, 'deps': [0]},
    {'id': 2, 'duration': 2, 'cpu': 1, 'deps': [0]},
    {'id': 3, 'duration': 4, 'cpu': 1, 'deps': [1, 2]},
]
CPU_LIMIT = 2
horizon = sum(t['duration'] for t in tasks_data)

# 2. Create the CP Model
model = cp_model.CpModel()

# 3. Create Interval Variables
# An "interval" automatically links Start, Duration, and End.
intervals = {}
starts = {}
ends = {}

for t in tasks_data:
    i = t['id']
    dur = t['duration']
    
    start_var = model.NewIntVar(0, horizon, f'start_{i}')
    end_var = model.NewIntVar(0, horizon, f'end_{i}')
    
    # Define the Interval: Fixed duration
    interval_var = model.NewIntervalVar(start_var, dur, end_var, f'interval_{i}')
    
    intervals[i] = interval_var
    starts[i] = start_var
    ends[i] = end_var

# 4. Add Constraints

# A. Precedence (DAG)
for t in tasks_data:
    for dep_id in t['deps']:
        # Start(Current) >= End(Dependency)
        model.Add(starts[t['id']] >= ends[dep_id])

# B. Cumulative Resource Constraint
# This is the "Magic" function. 
# We lists all intervals and their resource consumption (1 CPU each).
demands = [1 for _ in tasks_data]
model.AddCumulative(list(intervals.values()), demands, CPU_LIMIT)

# 5. Objective: Minimize Makespan
# Makespan = Max(End Times)
makespan = model.NewIntVar(0, horizon, 'makespan')
model.AddMaxEquality(makespan, list(ends.values()))
model.Minimize(makespan)

# 6. Solve
solver = cp_model.CpSolver()
status = solver.Solve(model)

if status == cp_model.OPTIMAL or status == cp_model.FEASIBLE:
    print(f"Min Makespan: {solver.Value(makespan)}")
