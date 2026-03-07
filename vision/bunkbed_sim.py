import numpy as np
from scipy.linalg import expm

# Constants from the GPU Core Strategy
friction_h = 2.0  # Decadic Friction (n ≡ 8 anchor)
superfluid_v = 0.5 # LSE Phase-Locked (Low resistance)

# Adjacency Matrix (A)
# Nodes: 0:u1, 1:u2 (Layer), 2:v1, 3:v2 (Posts)
A = np.array([
    [0, 1/friction_h, 1/superfluid_v, 0], # u1 connections
    [1/friction_h, 0, 0, 1/superfluid_v], # u2 connections
    [1/superfluid_v, 0, 0, 1/friction_h], # v1 connections
    [0, 1/superfluid_v, 1/friction_h, 0]  # v2 connections
])

# Degree Matrix (D)
D = np.diag(np.sum(A, axis=1))

# Laplacian (L)
L = D - A

# Simulate Connectivity at Steady State (t=1)
P = expm(-L)

print(f"P_stay (Horizontal): {P[0,1]:.4f}")
print(f"P_jump (Vertical):   {P[0,2]:.4f}")