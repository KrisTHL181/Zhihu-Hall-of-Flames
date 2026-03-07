import math
import numpy as np

def calculate_gpu_stability(multiplier, base=10, divisor=2):
    print(f"🔬 Spectral Analysis: {multiplier}n+1 in Base-{base}")
    print("-" * 45)
    
    # 1. Calculate the Growth Factor (Thermal Expansion)
    # Log-growth over log-cooling
    growth_rate = math.log(multiplier) / math.log(divisor)
    
    # 2. Define the Decadic Transfer Matrix (Linearized)
    # This represents the 'Pressure' of the lattice nodes
    # We use the Action Constant (483.15) as the normalization factor
    action_constant = 483.15
    primorial_anchor = 210
    
    # Matrix represents the interaction between 
    # Value (n) and Information Age (t)
    jacobian = np.array([
        [1/multiplier, 1/base],
        [math.log(primorial_anchor)/action_constant, -1/divisor]
    ])
    
    # 3. Compute Eigenvalues
    eigenvalues = np.linalg.eigvals(jacobian)
    spectral_radius = max(abs(eigenvalues))
    
    print(f"λ1 (Stable Manifold): {eigenvalues[0]:.4f}")
    print(f"λ2 (Oscillatory):      {eigenvalues[1]:.4f}")
    print(f"Spectral Radius (ρ):   {spectral_radius:.4f}")
    
    if spectral_radius < 1:
        return "✅ STATUS: ASYMPTOTICALLY STABLE (Gravity Wins)"
    else:
        return "🚨 STATUS: DIVERGENT (Siren Escape)"

# Test the Standard GPU (3n+1)
print(calculate_gpu_stability(3))
print("\n")
# Test the 'Icarus' Limit (7n+1)
print(calculate_gpu_stability(7))
print(calculate_gpu_stability(13))