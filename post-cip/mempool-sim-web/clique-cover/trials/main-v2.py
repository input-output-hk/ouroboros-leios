import pandas as pd
import numpy as np
import networkx as nx
from ortools.sat.python import cp_model


def optimize_subgraph_for_similarity(
    distance_matrix, node_names, D_max, a, s_min, timeout_seconds=0
):
    """
    Solves the clique cover integer program with a modified objective:
    Maximizes the intra-cluster similarity to ensure nodes with the highest
    number of shared transactions are grouped together.
    """
    M = len(distance_matrix)
    min_coverage = int(np.ceil((1 - a) * M))
    K = M // s_min

    if K == 0:
        return None

    model = cp_model.CpModel()

    # --- Variables ---
    # x[i, c] = 1 if mempool i is in cluster c
    x = {}
    for i in range(M):
        for c in range(K):
            x[i, c] = model.NewBoolVar(f"x_{i}_{c}")

    # y[c] = 1 if cluster c is active
    y = [model.NewBoolVar(f"y_{c}") for c in range(K)]

    # --- Standard Constraints ---
    # 1. Disjoint: Each node in at most one cluster
    for i in range(M):
        model.Add(sum(x[i, c] for c in range(K)) <= 1)

    # 2. Coverage: Must cluster at least (1 - a) of the nodes
    model.Add(sum(x[i, c] for i in range(M) for c in range(K)) >= min_coverage)

    # 3. Validity & Minimum Size
    for c in range(K):
        cluster_size = sum(x[i, c] for i in range(M))
        model.Add(cluster_size >= s_min * y[c])
        model.Add(cluster_size <= M * y[c])

    # 4. Diameter Constraint: Incompatible nodes cannot share a cluster
    for i in range(M):
        for j in range(i + 1, M):
            if distance_matrix[i][j] > D_max:
                for c in range(K):
                    model.AddImplication(x[i, c], x[j, c].Not())

    # 5. Symmetry Breaking (Performance boost)
    for c in range(K - 1):
        model.Add(y[c] >= y[c + 1])

    # --- THE NEW OBJECTIVE: Maximize Similarity ---
    # We create an auxiliary variable z[i,j,c] that equals 1 ONLY IF
    # both node i and node j are in cluster c.
    z = {}
    objective_terms = []

    for c in range(K):
        for i in range(M):
            for j in range(i + 1, M):
                dist = distance_matrix[i][j]

                if dist < D_max:
                    # Calculate how "similar" they are compared to the threshold
                    similarity_weight = int(D_max - dist)

                    if similarity_weight > 0:
                        z[i, j, c] = model.NewBoolVar(f"z_{i}_{j}_{c}")

                        # z can only be 1 if BOTH x[i,c] and x[j,c] are 1.
                        # Since we are maximizing, the solver wants z to be 1.
                        # These two upper bounds force z to 0 if either node is missing.
                        model.AddImplication(z[i, j, c], x[i, c])
                        model.AddImplication(z[i, j, c], x[j, c])

                        # Multiply the boolean by the weight
                        objective_terms.append(similarity_weight * z[i, j, c])

    # We maximize the total similarity.
    # We also subtract the sum of y (number of clusters) as a tiny tie-breaker penalty.
    # This tells the solver: "Maximize shared transactions first. If there's a tie, use fewer clusters."
    model.Maximize(sum(objective_terms) - sum(y))

    # --- Solve ---
    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = timeout_seconds
    solver.parameters.log_search_progress = True
    status = solver.Solve(model)

    # --- Extract ---
    if status in [cp_model.OPTIMAL, cp_model.FEASIBLE]:
        clusters = []
        for c in range(K):
            if solver.Value(y[c]) == 1:
                current_cluster = [
                    node_names[i] for i in range(M) if solver.Value(x[i, c]) == 1
                ]
                clusters.append(current_cluster)
        return clusters

    return None


def read_mempool_tsv(filepath):
    """Reads TSV, standardizes columns, and removes duplicates."""
    print(f"Reading data from {filepath}...")
    df = pd.read_csv(filepath, sep="\t")
    df.columns = df.columns.str.strip()
    if "Node ID" in df.columns and "TxId" in df.columns:
        df = df.rename(columns={"Node ID": "Node", "TxId": "Transaction"})

    initial_len = len(df)
    df = df.drop_duplicates()
    print(
        f"Successfully loaded {len(df)} unique pairs (Dropped {initial_len - len(df)} duplicates).\n"
    )
    return df


def build_distance_matrix(df):
    """Calculates symmetric difference distance using fast matrix math."""
    print("Building incidence matrix...")
    incidence_df = pd.crosstab(df["Node"], df["Transaction"])
    A = incidence_df.to_numpy(dtype=np.int16)
    node_names = incidence_df.index.tolist()

    print("Calculating pairwise distances (symmetric difference)...")
    intersections = A.dot(A.T)
    mempool_sizes = intersections.diagonal()

    distance_matrix = (
        mempool_sizes[:, None] + mempool_sizes[None, :] - 2 * intersections
    )
    max_transactions_N = mempool_sizes.max()
    print(f"Max transactions in any single mempool (N): {max_transactions_N}\n")
    return distance_matrix, node_names, max_transactions_N


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
        valid_subgraphs.append(
            {"node_names": sub_names, "sub_matrix": sub_matrix, "size": len(comp_list)}
        )

    print(f"Found {len(valid_subgraphs)} solvable sub-graphs (size >= {s_min}).")
    print(
        f"Discarded {orphaned_nodes} nodes that cannot possibly form a valid cluster.\n"
    )
    valid_subgraphs.sort(key=lambda x: x["size"], reverse=True)
    return valid_subgraphs


if __name__ == "__main__":
    FILE_PATH = "trial=2-slot=13.tsv"
    FILE_PATH = "nodes-100.tsv"
    EPSILON = 0.25  # Max allowed difference as a fraction of N
    A_FRAC = 0.10  # 1 - 0.10 = 90% coverage required within each sub-graph
    S_MIN = 50  # Minimum nodes per cluster
    SOLVER_TIMEOUT = 600  # Seconds to give the solver per sub-graph

    try:
        df = read_mempool_tsv(FILE_PATH)
    except FileNotFoundError:
        print(
            f"File '{FILE_PATH}' not found. Please ensure it is in the same directory."
        )
        exit()

    # Create a mapping of Node -> set of transactions for later intersection calculations
    node_to_txs = df.groupby("Node")["Transaction"].apply(set).to_dict()

    dist_matrix, all_nodes, N = build_distance_matrix(df)

    D_max_threshold = EPSILON * N
    print(
        f"Calculated D_max (Maximum allowed difference): {D_max_threshold:.2f} transactions\n"
    )

    subgraphs = extract_solvable_components(
        dist_matrix, all_nodes, D_max_threshold, S_MIN
    )

    all_final_clusters = []

    print("=== Beginning Optimization Pipeline ===")
    for idx, sg in enumerate(subgraphs):
        print(
            f"Solving Sub-graph {idx+1}/{len(subgraphs)} (Size: {sg['size']} nodes)..."
        )

        clusters = optimize_subgraph_for_similarity(
            distance_matrix=sg["sub_matrix"],
            node_names=sg["node_names"],
            D_max=D_max_threshold,
            a=A_FRAC,
            s_min=S_MIN,
            timeout_seconds=SOLVER_TIMEOUT,
        )

        if clusters:
            print(f"  -> Found {len(clusters)} clusters.")
            all_final_clusters.extend(clusters)
        else:
            print("  -> Solver timed out or found no feasible solution.")

    print("\n=== FINAL CLUSTERING SUMMARY ===")
    print(f"Total Clusters Formed: {len(all_final_clusters)}")
    total_clustered_nodes = sum(len(c) for c in all_final_clusters)
    print(f"Total Nodes Clustered: {total_clustered_nodes} / {len(all_nodes)}")

    for i, cluster in enumerate(all_final_clusters):
        # Calculate the multi-way intersection of all transactions shared by the cluster
        if cluster:
            shared_txs = set.intersection(*(node_to_txs[node] for node in cluster))
            num_shared = len(shared_txs)
        else:
            num_shared = 0

        print(
            f"Cluster {i+1} (Size: {len(cluster)} nodes, Shared Txs: {num_shared}): {cluster[:5]}..."
        )
