import pulp
import shutil
import sys

# 1. Dynamically find the path to the HiGHS binary
# shutil.which searches your PATH (which Nix sets up correctly)
highs_path = shutil.which("highs")

if highs_path is None:
    print("Error: Could not find 'highs' in PATH. Is it installed in your nix-shell?")
    sys.exit(1)

print(f"Found HiGHS at: {highs_path}")

# 2. Configure the solver with this explicit path
# We use HiGHS_CMD, passing the path argument.
# You can also pass options=['presolve=on'] etc.
solver = pulp.HiGHS_CMD(path=highs_path, msg=True)



# ==========================================
# 1. SETUP THE DATA & MODEL
# ==========================================

# Parameters
N_SLOTS = 10       # Max capacity of the block (Keep small for testing)
C_CPUS = 2         # Number of parallel CPUs for Phase 1
V_PHASE1 = 5.0     # Time for Phase 1 validation (fixed)
A_APPLY = 1.0      # Time for Ledger Application (fixed)
P_BUDGET = 20.0    # Total budget for Phase 2 processing

# Create the Linear Programming Problem (Maximization)
prob = pulp.LpProblem("Cardano_Worst_Case_Analysis", pulp.LpMaximize)

# ==========================================
# 2. DEFINE VARIABLES
# ==========================================

# x[i]: Binary. 1 if transaction i exists, 0 otherwise.
x = pulp.LpVariable.dicts("x", range(N_SLOTS), cat='Binary')

# p[i]: Continuous. The Phase 2 duration of transaction i.
p = pulp.LpVariable.dicts("p", range(N_SLOTS), lowBound=0, upBound=P_BUDGET)

# t1[i]: Continuous. Time when Phase 1 finishes for tx i.
t1 = pulp.LpVariable.dicts("t1", range(N_SLOTS), lowBound=0)

# t2[i]: Continuous. Time when Phase 2 (and Apply) finishes for tx i.
t2 = pulp.LpVariable.dicts("t2", range(N_SLOTS), lowBound=0)

# ==========================================
# 3. ADD CONSTRAINTS
# ==========================================

# --- A. Global Limits ---
# The sum of all Phase 2 times must be <= Budget
prob += pulp.lpSum([p[i] for i in range(N_SLOTS)]) <= P_BUDGET

# --- B. Logical Consistency ---
for i in range(N_SLOTS):
    # If transaction i does not exist (x=0), its processing time p must be 0
    prob += p[i] <= P_BUDGET * x[i]
    
    # Contiguity: You can't have transaction i+1 if you don't have transaction i.
    # This prevents "gaps" in the block, simplifying the pipeline logic.
    if i < N_SLOTS - 1:
        prob += x[i] >= x[i+1]

# --- C. Phase 1 Pipeline (Parallel CPUs) ---
for i in range(N_SLOTS):
    # Determine the start time for Phase 1 on this specific CPU.
    # If i < C_CPUS, this is the first batch; they start at t=0.
    # Otherwise, it must wait for the previous user of this CPU (i - C_CPUS).
    
    if i < C_CPUS:
        # First batch: Finish time is simply V (if it exists)
        prob += t1[i] == V_PHASE1 * x[i]
    else:
        # Subsequent batches: Finish time >= Previous finish + V
        # Note: If x[i]=0, t1[i] is forced to match t1[i-C]. This effectively
        # "freezes" the timeline for that CPU slot, which is harmless since 
        # it won't trigger any t2 events.
        prob += t1[i] >= t1[i - C_CPUS] + (V_PHASE1 * x[i])

# --- D. Phase 2 Sequencer (Serial) ---
for i in range(N_SLOTS):
    # Constraint D1: Must wait for OWN Phase 1 to finish
    prob += t2[i] >= t1[i] + p[i] + (A_APPLY * x[i])
    
    # Constraint D2: Must wait for PREVIOUS Phase 2 to finish
    if i == 0:
        # First transaction doesn't wait for a previous one
        pass 
    else:
        prob += t2[i] >= t2[i-1] + p[i] + (A_APPLY * x[i])

# ==========================================
# 4. OBJECTIVE FUNCTION
# ==========================================
# We want to maximize the finish time of the LAST active transaction.
# Since we forced contiguity (x[i] >= x[i+1]), the "last active" is implicitly
# handled by the chain of dependencies. If we maximize the sum of all t2, 
# or just the last t2, the solver will push the active ones to be as late as possible.
# A safe bet is to maximize the t2 of the very last slot. Even if x[N-1]=0,
# the constraints link it back to the last *real* completion time.

prob += t2[N_SLOTS - 1]

# ==========================================
# 5. SOLVE
# ==========================================

# OPTION A: Use Default Solver (CBC) - No setup required
print("Solving with default solver...")
status = prob.solve(solver)

# OPTION B: Use HiGHS (Uncomment if installed)
# path_to_highs = "highs" # Or full path e.g. /usr/bin/highs
# solver = pulp.getSolver('HiGHS', path=path_to_highs)
# status = prob.solve(solver)

# ==========================================
# 6. PRINT RESULTS
# ==========================================

print(f"Status: {pulp.LpStatus[status]}")
print(f"Worst-Case Delay (Objective): {pulp.value(prob.objective):.2f} seconds")

print("\n--- The Adversarial Block Structure ---")
print(f"{'Tx ID':<5} | {'Exist?':<6} | {'CPU':<3} | {'Phase 1 End':<11} | {'Phase 2 Len':<11} | {'Phase 2 End':<11}")
print("-" * 65)

for i in range(N_SLOTS):
    vx = pulp.value(x[i])
    if vx > 0.5: # Floating point tolerance check for binary
        vp = pulp.value(p[i])
        vt1 = pulp.value(t1[i])
        vt2 = pulp.value(t2[i])
        cpu_id = i % C_CPUS
        print(f"{i:<5} | {int(vx):<6} | {cpu_id:<3} | {vt1:<11.2f} | {vp:<11.2f} | {vt2:<11.2f}")
