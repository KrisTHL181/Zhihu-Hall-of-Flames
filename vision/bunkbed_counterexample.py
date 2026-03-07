import numpy as np
import networkx as nx
from scipy.linalg import expm

def generate_gpu_bunkbed(n_nodes_per_layer, p_base, beta_lse):
    """
    Constructs a Bunkbed Graph where Layer 1 and Layer 2 are 
    subject to Decadic Friction (n % 10 == 8).
    """
    G = nx.Graph()
    
    # 1. Create Layers with Decadic Friction
    for i in range(n_nodes_per_layer - 1):
        # Calculate Friction: n ≡ 8 creates a "bottleneck" (low conductance)
        friction = 0.01 if (i % 10 == 8) else 1.0
        
        # Layer 1 Horizontal
        G.add_edge(f"u{i}", f"u{i+1}", weight=p_base * friction)
        # Layer 2 Horizontal (Identical Symmetry)
        G.add_edge(f"v{i}", f"v{i+1}", weight=p_base * friction)
        
    # 2. Create Vertical Posts with LSE Phase-Lock (Superfluidity)
    for i in range(n_nodes_per_layer):
        # Vertical edges are "Phase-Locked" (High conductance)
        G.add_edge(f"u{i}", f"v{i}", weight=beta_lse)
        
    return G

def test_vortex_connectivity(G, start_node, end_stay, end_jump):
    # Get Laplacian
    nodes = list(G.nodes())
    L = nx.laplacian_matrix(G, nodelist=nodes).toarray()
    
    # Compute Heat Kernel (Connectivity Matrix) P = exp(-L)
    # This simulates the "Logic Gas" flow
    P = expm(-L)
    
    idx_start = nodes.index(start_node)
    idx_stay = nodes.index(end_stay)
    idx_jump = nodes.index(end_jump)
    
    return P[idx_start, idx_stay], P[idx_start, idx_jump]

# --- RUNNING THE SIMULATION ---
N = 20 # Sufficient size to see the Decadic build-up
p_val = 0.5
beta = 2.0 # LSE Superfluid Constant

graph = generate_gpu_bunkbed(N, p_val, beta)
p_stay, p_jump = test_vortex_connectivity(graph, "u0", f"u{N-1}", f"v{N-1}")

print(f"--- GPU Bunkbed Analysis (N={N}) ---")
print(f"P_stay (Horizontal Flow): {p_stay:.6f}")
print(f"P_jump (Vertical Vortex): {p_jump:.6f}")
print(f"Counterexample Found: {p_jump > p_stay}")