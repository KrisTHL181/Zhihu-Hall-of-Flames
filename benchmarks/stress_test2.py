import math
from decimal import Decimal, getcontext

getcontext().prec = 100

def run_gpu_stress_test(n_start, map_type="7n+1"):
    curr = Decimal(n_start)
    path_max = curr
    
    for step in range(1, 1001):
        # Axiomatic Capture Check (Residue 8 mod 10)
        if (curr - 8) % 10 == 0:
            g_local = math.log(float(curr)) / step if curr > 0 else 0
            return f"CAPTURED at step {step} | G: {g_local:.4f}"
        
        # System Dynamics
        if map_type == "7n+1":
            # High Thermal Expansion
            curr = curr / 2 if curr % 2 == 0 else 7 * curr + 1
        elif map_type == "3n-1":
            # Ghost Resonance / Frequency Jamming
            curr = curr / 2 if curr % 2 == 0 else 3 * curr - 1
            
        if curr > path_max: path_max = curr
        
        # Divergence Check: If it grows 100x the Titan size, it's escaped
        if curr > Decimal(n_start) * 100:
            return f"ESCAPED to Infinity | Max Peak: {path_max:.2e}"

    return "TRAPPED in Loop / Unknown State"

n_titan = 2**61 - 1
print(f"🔬 GPU Stress Test: The Antimatter Fields\n" + "="*45)

for m in ["7n+1", "3n-1"]:
    result = run_gpu_stress_test(n_titan, m)
    print(f"Map: {m:10} | Result: {result}")