import pandas as pd
import numpy as np
import matplotlib.pyplot as plt
import igraph as ig
import leidenalg

def read_mempool_tsv(filepath):
    """Reads TSV, standardizes columns, and removes duplicates."""
    print(f"Reading data from {filepath}...")
    df = pd.read_csv(filepath, sep='\t')
    df.columns = df.columns.str.strip()
    if 'Node ID' in df.columns and 'TxId' in df.columns:
        df = df.rename(columns={'Node ID': 'Node', 'TxId': 'Transaction'})
    
    initial_len = len(df)
    df = df.drop_duplicates()
    print(f"Successfully loaded {len(df)} unique pairs (Dropped {initial_len - len(df)} duplicates).\n")
    return df

def build_distance_matrix(df):
    """Calculates symmetric difference distance and returns the incidence matrix."""
    print("Building incidence matrix...")
    incidence_df = pd.crosstab(df['Node'], df['Transaction'])
    A = incidence_df.to_numpy(dtype=np.int16)
    node_names = incidence_df.index.tolist()
    
    print("Calculating pairwise distances (symmetric difference)...")
    intersections = A.dot(A.T)
    mempool_sizes = intersections.diagonal()
    
    distance_matrix = mempool_sizes[:, None] + mempool_sizes[None, :] - 2 * intersections
    max_transactions_N = mempool_sizes.max()
    print(f"Max transactions in any single mempool (N): {max_transactions_N}\n")
    return distance_matrix, node_names, max_transactions_N, A

def visualize_incidence_matrix(A, filename="mempool_vs_transaction.png"):
    """
    Outputs a PNG file of the Mempool vs Transaction incidence matrix.
    0 = Black, 1 = White. Each entry is scaled to a 2x2 pixel block.
    """
    print(f"Generating incidence matrix visualization: {filename}...")
    A_scaled = np.kron(A, np.ones((2, 2)))
    
    fig, ax = plt.subplots(figsize=(12, 8))
    ax.imshow(A_scaled, cmap='gray', aspect='equal', interpolation='nearest')
    ax.set_ylabel("Mempool", fontsize=14, fontweight='bold')
    ax.set_xlabel("Transaction", fontsize=14, fontweight='bold')
    ax.set_xticks([])
    ax.set_yticks([])
    
    plt.tight_layout()
    plt.savefig(filename, dpi=300, bbox_inches='tight')
    plt.close(fig)
    print("Visualization saved successfully.\n")

def run_leiden_clustering(distance_matrix, node_names, D_max, s_min):
    """
    Builds a similarity graph and uses the Leiden algorithm to find 
    the optimal community partitions instantly.
    """
    print(f"Building similarity graph for Leiden (Threshold D_max = {D_max:.2f})...")
    M = len(distance_matrix)
    
    edges = []
    weights = []
    
    # Build edges only for valid pairs (d <= D_max)
    for i in range(M):
        for j in range(i + 1, M):
            d = distance_matrix[i][j]
            if d <= D_max:
                edges.append((i, j))
                # Weight formula: Highly identical nodes get massive weights. 
                # The +1 ensures that pairs sitting exactly at D_max still get a positive edge weight (1).
                similarity_weight = int(D_max - d + 1)
                weights.append(similarity_weight)
                
    print(f"Graph generated with {M} nodes and {len(edges)} valid edges.")
    
    # Load into iGraph (The C-engine that powers Leiden)
    g = ig.Graph(n=M, edges=edges)
    g.es['weight'] = weights
    
    print("Running Leiden algorithm (Modularity Maximization)...")
    # find_partition mathematically maximizes the density of weights inside the clusters
    partition = leidenalg.find_partition(g, leidenalg.ModularityVertexPartition, weights='weight')
    
    print(f"Leiden algorithm finished! Found {len(partition)} total topological communities.\n")
    
    # Filter out the "dust" (clusters smaller than our allowed minimum size)
    valid_clusters = []
    orphaned_nodes = 0
    
    for community in partition:
        if len(community) >= s_min:
            cluster_names = [node_names[idx] for idx in community]
            valid_clusters.append(cluster_names)
        else:
            orphaned_nodes += len(community)
            
    print(f"Filtered down to {len(valid_clusters)} valid clusters (Size >= {s_min}).")
    print(f"Discarded {orphaned_nodes} nodes that belonged to communities too small to qualify.\n")
    
    # Sort from largest cluster to smallest
    valid_clusters.sort(key=len, reverse=True)
    return valid_clusters

if __name__ == "__main__":
    FILE_PATH = "nodes-1000.tsv"
    FILE_PATH = "trial=2-slot=13.tsv"
    EPSILON = 0.25       # Max allowed difference to form an edge
    S_MIN = 50           # Minimum nodes per cluster to keep in the final summary
    
    try:
        df = read_mempool_tsv(FILE_PATH)
    except FileNotFoundError:
        print(f"File '{FILE_PATH}' not found. Please ensure it is in the same directory.")
        exit()

    # Create a mapping of Node -> set of transactions for intersection calculations
    node_to_txs = df.groupby('Node')['Transaction'].apply(set).to_dict()

    dist_matrix, all_nodes, N, A = build_distance_matrix(df)
    
    # Generate the visualization
    visualize_incidence_matrix(A, "mempool_vs_transaction.png")
    
    D_max_threshold = EPSILON * N
    
    # Run the Leiden optimization
    print("=== Beginning Leiden Community Detection ===")
    all_final_clusters = run_leiden_clustering(
        distance_matrix=dist_matrix, 
        node_names=all_nodes, 
        D_max=D_max_threshold, 
        s_min=S_MIN
    )

    print("=== FINAL CLUSTERING SUMMARY ===")
    print(f"Total Clusters Formed: {len(all_final_clusters)}")
    total_clustered_nodes = sum(len(c) for c in all_final_clusters)
    print(f"Total Nodes Clustered: {total_clustered_nodes} / {len(all_nodes)}")
    
    for i, cluster in enumerate(all_final_clusters):
        if cluster:
            shared_txs = set.intersection(*(node_to_txs[node] for node in cluster))
            num_shared = len(shared_txs)
        else:
            num_shared = 0
            
        print(f"Cluster {i+1} (Size: {len(cluster)} nodes, Shared Txs: {num_shared}): {cluster[:5]}...")
