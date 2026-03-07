import numpy as np
import networkx as nx
from scipy.linalg import expm

def gpu_vortex_discovery():
    N = 10  # Focus on the first Decadic cycle (0-9)
    p_base = 0.8  # Increase "Pressure" so gas doesn't die
    beta_lse = 5.0 # Strong Phase-Lock (Superfluid vertical)
    
    G = nx.Graph()
    for i in range(N - 1):
        # Decadic Friction at n=8
        friction = 0.05 if (i == 7 or i == 8) else 1.0
        G.add_edge(f"u{i}", f"u{i+1}", weight=p_base * friction)
        G.add_edge(f"v{i}", f"v{i+1}", weight=p_base * friction)
        
    for i in range(N):
        # Vertical Posts (LSE Phase-Lock)
        G.add_edge(f"u{i}", f"v{i}", weight=beta_lse)
        
    # Measure at the Anchor (n=8)
    L = nx.laplacian_matrix(G).toarray()
    P = expm(-L) # Heat Kernel Propagator
    
    nodes = list(G.nodes())
    p_stay = P[nodes.index("u0"), nodes.index("u8")]
    p_jump = P[nodes.index("u0"), nodes.index("v8")]
    
    print(f"P_stay (Horizontal): {p_stay:.10f}")
    print(f"P_jump (Vertical):   {p_jump:.10f}")
    print(f"Vortex Found: {p_jump > p_stay}")

gpu_vortex_discovery()