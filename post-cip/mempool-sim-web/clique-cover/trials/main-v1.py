import pandas as pd
import numpy as np
import networkx as nx
from ortools.sat.python import cp_model

# ==========================================
# 1. Read TSV File
# ==========================================
def read_mempool_tsv(filepath):
    """Reads TSV, standardizes columns, and removes duplicates."""
    print(f"Reading data from {filepath}...")
    df = pd.read_csv(filepath, sep='\t') # Handles variable whitespace/tabs
    
#   df.columns = df.columns.str.strip()
    # Map to standardized names
    if 'Node ID' in df.columns and 'TxId' in df.columns:
        df = df.rename(columns={'Node ID': 'Node', 'TxId': 'Transaction'})
    
    initial_len = len(df)
    df = df.drop_duplicates()
    print(f"Successfully loaded {len(df)} unique pairs (Dropped {initial_len - len(df)} duplicates).\n")
    return df

# ==========================================
# 2. Build Distance Matrix
# ==========================================
def build_distance_matrix(df):
    """Calculates symmetric difference distance using fast matrix math."""
    print("Building incidence matrix...")
    incidence_df = pd.crosstab(df['Node'], df['Transaction'])
    
    A = incidence_df.to_numpy(dtype=np.int16)
    node_names = incidence_df.index.tolist()
    
    print("Calculating pairwise distances (symmetric difference)...")
    intersections = A.dot(A.T)
    mempool_sizes = intersections.diagonal()
    
    # d_ij = |T_i| + |T_j| - 2|T_i ∩ T_j|
    distance_matrix = mempool_sizes[:, None] + mempool_sizes[None, :] - 2 * intersections
    
    # We also need the maximum mempool size (N) for our epsilon calculation
    max_transactions_N = mempool_sizes.max()
    print(f"Max transactions in any single mempool (N): {max_transactions_N}\n")
    
    return distance_matrix, node_names, max_transactions_N

# ==========================================
# 3. Extract Sub-Graphs (Connected Components)
# ==========================================
def extract_solvable_components(distance_matrix, node_names, D_max, s_min):
    """Breaks the massive distance matrix into solvable islands."""
    print(f"Shattering graph using threshold D_max = {D_max}...")
    
    adjacency_matrix = (distance_matrix <= D_max).astype(int)
    np.fill_diagonal(adjacency_matrix, 0)
    
    G = nx.from_numpy_array(adjacency_matrix)
    components = list(nx.connected_components(G))
    
    valid_subgraphs = []
    orphaned_nodes = 0
    
    for comp in components:
        comp_list = list(comp)
        if len(comp_list) < s_min:
            orphaned_nodes += len(comp_list)
            continue
            
        sub_names = [node_names[i] for i in comp_list]
        sub_matrix = distance_matrix[np.ix_(comp_list, comp_list)]
        
        valid_subgraphs.append({
            'node_names': sub_names,
            'sub_matrix': sub_matrix,
            'size': len(comp_list)
        })
        
    print(f"Found {len(valid_subgraphs)} solvable sub-graphs (size >= {s_min}).")
    print(f"Discarded {orphaned_nodes} nodes that cannot possibly form a valid cluster.\n")
    
    # Tackle the hardest problems first
    valid_subgraphs.sort(key=lambda x: x['size'], reverse=True)
    return valid_subgraphs

# ==========================================
# 4. OR-Tools Optimizer (Runs on Sub-Graphs)
# ==========================================
def optimize_subgraph(distance_matrix, node_names, D_max, a, s_min, timeout_seconds=0):
    """Solves the clique cover integer program for a single sub-graph."""
    M = len(distance_matrix)
    min_coverage = int(np.ceil((1 - a) * M))
    K = M // s_min 
    
    if K == 0: return None

    model = cp_model.CpModel()
    x = {}
    for i in range(M):
        for c in range(K):
            x[i, c] = model.NewBoolVar(f'x_{i}_{c}')
    y = [model.NewBoolVar(f'y_{c}') for c in range(K)]

    # Constraints
    for i in range(M):
        model.Add(sum(x[i, c] for c in range(K)) <= 1)
        
    model.Add(sum(x[i, c] for i in range(M) for c in range(K)) >= min_coverage)

    for i in range(M):
        for j in range(i + 1, M):
            if distance_matrix[i][j] > D_max:
                for c in range(K):
                    model.AddImplication(x[i, c], x[j, c].Not())

    for c in range(K):
        cluster_size = sum(x[i, c] for i in range(M))
        model.Add(cluster_size >= s_min * y[c])
        model.Add(cluster_size <= M * y[c])

    for c in range(K - 1):
        model.Add(y[c] >= y[c + 1])

    # Objective
    model.Minimize(sum(y))

    # Solve
    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = timeout_seconds
    solver.parameters.log_search_progress = True
    status = solver.Solve(model)

    # Extract
    if status in [cp_model.OPTIMAL, cp_model.FEASIBLE]:
        num_clusters = int(solver.ObjectiveValue())
        clusters = []
        for c in range(num_clusters):
            current_cluster = [node_names[i] for i in range(M) if solver.Value(x[i, c]) == 1]
            if current_cluster:
                clusters.append(current_cluster)
        return clusters
    return None

# ==========================================
# 5. Main Execution Pipeline
# ==========================================
if __name__ == "__main__":
    # --- Configuration ---
    FILE_PATH = "nodes-1000.tsv"
    FILE_PATH = "trial=2-slot=13.tsv"
    EPSILON = 0.25       # Max allowed difference as a fraction of N
    A_FRAC = 0.10        # 1 - 0.10 = 90% coverage required within each sub-graph
    S_MIN = 1000         # Minimum nodes per cluster
    SOLVER_TIMEOUT = 300 # Seconds to give the solver per sub-graph
    
    # --- Pipeline ---
    try:
        df = read_mempool_tsv(FILE_PATH)
    except FileNotFoundError:
        print(f"File {FILE_PATH} not found. Please ensure the path is correct.")
        exit()

    dist_matrix, all_nodes, N = build_distance_matrix(df)
    
    D_max_threshold = EPSILON * N
    print(f"Calculated D_max (Maximum allowed difference): {D_max_threshold:.2f} transactions\n")
    
    subgraphs = extract_solvable_components(
        dist_matrix, all_nodes, D_max_threshold, S_MIN
    )
    
    all_final_clusters = []
    
    print("=== Beginning Optimization Pipeline ===")
    for idx, sg in enumerate(subgraphs):
        print(f"Solving Sub-graph {idx+1}/{len(subgraphs)} (Size: {sg['size']} nodes)...")
        
        clusters = optimize_subgraph(
            distance_matrix=sg['sub_matrix'],
            node_names=sg['node_names'],
            D_max=D_max_threshold,
            a=A_FRAC,
            s_min=S_MIN,
            timeout_seconds=SOLVER_TIMEOUT
        )
        
        if clusters:
            print(f"  -> Found {len(clusters)} clusters.")
            all_final_clusters.extend(clusters)
        else:
            print("  -> Solver timed out or found no feasible solution.")

    # --- Summary ---
    print("\n=== FINAL CLUSTERING SUMMARY ===")
    print(f"Total Clusters Formed: {len(all_final_clusters)}")
    total_clustered_nodes = sum(len(c) for c in all_final_clusters)
    print(f"Total Nodes Clustered: {total_clustered_nodes} / {len(all_nodes)}")
    
    # Print the first few clusters as an example
    for i, cluster in enumerate(all_final_clusters[:5]):
        print(f"Cluster {i+1} (Size: {len(cluster)}): {cluster[:5]}...")
