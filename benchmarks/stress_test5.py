import math
from decimal import Decimal, getcontext

getcontext().prec = 100

def test_icarus_tunneling(n_start, k_val):
    curr = Decimal(n_start)
    initial_mass = curr.ln()
    
    print(f"🚀 Launching Icarus (k={k_val}) | Start Mass: {initial_mass:.2f}")
    
    for step in range(1, 2000):
        # The Axiomatic Check
        if (curr - 8) % 10 == 0:
            return f"❌ CAPTURED at step {step} (Gravity Wins)"
        
        # The Icarus Dynamics (3n + k)
        if curr % 2 == 0:
            curr //= 2
        else:
            curr = 3 * curr + k_val
            
        # Growth Check: If it triples the starting bit-length, it's tunneling
        if curr.ln() > initial_mass * 3:
            return f"🚨 TUNNELING DETECTED | Step {step} | Current Mass: {curr.ln():.2f}"

    return "⏳ ORBITAL STALL (Likely a Loop)"

# Test with various 'k' constants to find the "Melt Point"
n_titan = 2**61 - 1
k_tests = [1, 7, 13, 211, 1000003] # Note: 211 is just above our Primorial Anchor P4 (210)

print("🔬 GPU Tunneling Experiment")
print("="*45)
for k in k_tests:
    result = test_icarus_tunneling(n_titan, k)
    print(f"Constant k={k:7} | {result}")