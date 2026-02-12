import pulp
import shutil
import sys

# ==========================================
# 0. SOLVER SETUP (NixOS / venv safe)
# ==========================================
highs_path = shutil.which("highs")
cbc_path = shutil.which("cbc")
solver = None

if highs_path:
    print(f"Found HiGHS at: {highs_path}")
    # msg=False reduces the massive log output
    solver = pulp.HiGHS_CMD(path=highs_path, msg=False)
else:
    print("Warning: HiGHS not found. Falling back to default CBC (slower).")
    solver = pulp.COIN_CMD(path=cbc_path, msg=False)

# ==========================================
# 1. MODEL DATA
# ==========================================
N_SLOTS = 10       
C_CPUS = 2        
V_PHASE1 = 5.0     
A_APPLY = 1.0      
P_BUDGET = 20.0    
BIG_M = 1000.0     # A constant larger than any possible makespan

prob = pulp.LpProblem("Cardano_Adversarial_Analysis", pulp.LpMaximize)

# ==========================================
# 2. VARIABLES
# ==========================================
x = pulp.LpVariable.dicts("x", range(N_SLOTS), cat='Binary')
p = pulp.LpVariable.dicts("p", range(N_SLOTS), lowBound=0, upBound=P_BUDGET)

# t1: Phase 1 Finish Time. 
# t2: Phase 2 Finish Time.
t1 = pulp.LpVariable.dicts("t1", range(N_SLOTS), lowBound=0)
t2 = pulp.LpVariable.dicts("t2", range(N_SLOTS), lowBound=0)

# s2: Start Time of Phase 2 (Helper variable)
s2 = pulp.LpVariable.dicts("s2", range(N_SLOTS), lowBound=0)

# is_waiting_for_cpu: Binary switch for the MAX function
# 1 = Phase 2 must wait for Phase 1 (CPU limited)
# 0 = Phase 2 must wait for Previous Phase 2 (Sequence limited)
wait_cpu = pulp.LpVariable.dicts("wait_cpu", range(N_SLOTS), cat='Binary')

# ==========================================
# 3. CONSTRAINTS
# ==========================================

# --- A. Global Budgets ---
prob += pulp.lpSum([p[i] for i in range(N_SLOTS)]) <= P_BUDGET

# --- B. Logical Consistency ---
for i in range(N_SLOTS):
    prob += p[i] <= P_BUDGET * x[i]
    if i < N_SLOTS - 1:
        prob += x[i] >= x[i+1] # No gaps allowed

# --- C. Phase 1 Exact Timing (Equality) ---
# Since we forced no gaps, we can calculate t1 strictly without inequalities.
# t1[i] = V * (number of active items assigned to this CPU so far)
for i in range(N_SLOTS):
    # Find all previous slots that share this CPU (j % C == i % C)
    cpu_peers = [x[j] for j in range(i + 1) if j % C_CPUS == i % C_CPUS]
    prob += t1[i] == V_PHASE1 * pulp.lpSum(cpu_peers)

# --- D. Phase 2 Exact Timing (Big-M Logic) ---
# Logic: start_time[i] = max(t1[i], t2[i-1])
# We enforce this exactly using the binary 'wait_cpu' variable.

for i in range(N_SLOTS):
    prev_finish = t2[i-1] if i > 0 else 0
    
    # 1. Lower Bounds (Standard)
    prob += s2[i] >= t1[i]
    prob += s2[i] >= prev_finish
    
    # 2. Upper Bounds (The "Tightening" Constraints)
    # If wait_cpu=1: s2 <= t1 + 0  AND s2 <= prev + BigM  -> Forces s2 = t1
    # If wait_cpu=0: s2 <= t1 + BigM AND s2 <= prev + 0   -> Forces s2 = prev
    prob += s2[i] <= t1[i] + BIG_M * (1 - wait_cpu[i])
    prob += s2[i] <= prev_finish + BIG_M * wait_cpu[i]

    # 3. Definition of Finish Time
    prob += t2[i] == s2[i] + p[i] + (A_APPLY * x[i])

# ==========================================
# 4. OBJECTIVE
# ==========================================
prob += t2[N_SLOTS - 1]

# ==========================================
# 5. SOLVE & OUTPUT
# ==========================================
status = prob.solve(solver)

print(f"Status: {pulp.LpStatus[status]}")

if status == pulp.LpStatusOptimal:
    print(f"Worst-Case Delay: {pulp.value(prob.objective):.2f}s")
    print("\nAdversarial Block Schedule:")
    print(f"{'ID':<3} {'Exist':<5} {'CPU':<3} {'P1 End':<8} {'Start2':<8} {'P2 Len':<8} {'P2 End':<8}")
    print("-" * 55)
    for i in range(N_SLOTS):
        if pulp.value(x[i]) > 0.5:
            print(f"{i:<3} {int(pulp.value(x[i])):<5} {i%C_CPUS:<3} "
                  f"{pulp.value(t1[i]):<8.1f} {pulp.value(s2[i]):<8.1f} "
                  f"{pulp.value(p[i]):<8.1f} {pulp.value(t2[i]):<8.1f}")
else:
    print("Solver failed to find an optimal solution.")
