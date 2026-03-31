import pandas as pd
import numpy as np
import networkx as nx
from ortools.sat.python import cp_model


def optimize_subgraph_facility_location(
    distance_matrix, node_names, D_max, a, s_min, timeout_seconds=0
):
    """
    Solves the Facility Location integer program:
    Elects 'Centers' (Medoids) and assigns nodes to those centers.
    Guarantees no chaining and maximizes similarity to the cluster's center.
    """
    M = len(distance_matrix)
    min_coverage = int(np.ceil((1 - a) * M))

    model = cp_model.CpModel()

    # --- Variables ---
    # y[j] = 1 if node j is elected as a cluster center
    y = [model.NewBoolVar(f"y_{j}") for j in range(M)]

    # x[i, j] = 1 if node i is assigned to center j
    x = {}
    valid_j_for_i = {i: [] for i in range(M)}
    valid_i_for_j = {j: [] for j in range(M)}

    # Massive Memory Optimization:
    # Only create boolean variables for pairs that are legally allowed to connect
    for i in range(M):
        for j in range(M):
            if distance_matrix[i][j] <= D_max:
                x[i, j] = model.NewBoolVar(f"x_{i}_{j}")
                valid_j_for_i[i].append(j)
                valid_i_for_j[j].append(i)

    # --- Constraints ---

    # 1. Disjoint: A node can be assigned to AT MOST 1 center
    for i in range(M):
        model.Add(sum(x[i, j] for j in valid_j_for_i[i]) <= 1)

    # 2. Validity: A node can only be assigned to j if j is an active center
    for i in range(M):
        for j in valid_j_for_i[i]:
            model.AddImplication(x[i, j], y[j])

    # 3. Center Logic: If j is a center, it must be assigned to itself
    for j in range(M):
        model.Add(x[j, j] == y[j])

    # 4. Coverage: Must cluster at least (1 - a) of the nodes
    model.Add(sum(x[i, j] for i in range(M) for j in valid_j_for_i[i]) >= min_coverage)

    # 5. Minimum Size: If j is a center, its cluster must have at least s_min nodes
    for j in range(M):
        cluster_size = sum(x[i, j] for i in valid_i_for_j[j])
        model.Add(cluster_size >= s_min * y[j])
        # Upper bound constraint just ties the logic together
        model.Add(cluster_size <= M * y[j])

    # --- THE OBJECTIVE: Maximize Similarity to the Center ---
    objective_terms = []

    for i in range(M):
        for j in valid_j_for_i[i]:
            # Nodes assigned to a center exactly identical to them get highest reward
            similarity_weight = int(D_max - distance_matrix[i][j])
            objective_terms.append(similarity_weight * x[i, j])

    # Maximize total similarity, minus a small penalty for the number of centers
    # to encourage fewer, denser clusters when similarities are tied.
    model.Maximize(sum(objective_terms) - sum(y))

    # --- Solve ---
    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = timeout_seconds
    solver.parameters.log_search_progress = True
    status = solver.Solve(model)

    # --- Extract ---
    if status in [cp_model.OPTIMAL, cp_model.FEASIBLE]:
        clusters = []
        for j in range(M):
            if solver.Value(y[j]) == 1:
                # Reconstruct the cluster based on nodes assigned to center j
                current_cluster = [
                    node_names[i]
                    for i in valid_i_for_j[j]
                    if solver.Value(x[i, j]) == 1
                ]
                if current_cluster:
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
    """Calculates symmetric difference distance and returns the incidence matrix."""
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
    EPSILON = 0.25  # Max allowed difference to the CENTER node
    A_FRAC = 0.10  # 1 - 0.10 = 90% coverage required within each sub-graph
    S_MIN = 1  # Minimum nodes per cluster
    SOLVER_TIMEOUT = 600  # Seconds to give the solver per sub-graph

    try:
        df = read_mempool_tsv(FILE_PATH)
    except FileNotFoundError:
        print(
            f"File '{FILE_PATH}' not found. Please ensure it is in the same directory."
        )
        exit()

    # Create a mapping of Node -> set of transactions for intersection calculations
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

        clusters = optimize_subgraph_facility_location(
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
        if cluster:
            shared_txs = set.intersection(*(node_to_txs[node] for node in cluster))
            num_shared = len(shared_txs)
        else:
            num_shared = 0

        print(
            f"Cluster {i+1} (Size: {len(cluster)} nodes, Shared Txs: {num_shared}): {cluster[:5]}..."
        )
