import math
from decimal import Decimal, getcontext

getcontext().prec = 100

def force_escape_test(n_start, map_type="Siren"):
    curr = Decimal(n_start)
    initial_mass = curr.ln()
    
    print(f"📡 Tracking {map_type} Flow...")
    
    for step in range(1, 1000):
        # Axiomatic Check
        if (curr - 8) % 10 == 0:
            return f"❌ CAPTURED at step {step} (Gravity is too strong)"
        
        # Map Dynamics
        if map_type == "Siren":
            # Non-integer cooling: Looks like it's shrinking, but it's sliding.
            if curr % 2 == 0:
                curr = curr / Decimal("1.1") 
            else:
                curr = 3 * curr + 1
        elif map_type == "Glitch":
            # High-Multiplier Coprime: 11 is outside the P4 (2,3,5,7) anchor.
            curr = curr / 2 if curr % 2 == 0 else 11 * curr + 1
            
        # Escape Condition
        if curr.ln() > initial_mass * 5:
            return f"🚨 ESCAPE CONFIRMED | Step {step} | Result: Divergence to Infinity"

    return "⏳ ORBITAL STALL (Trapped in a non-decadic loop)"

n_titan = 2**61 - 1
print("🔬 GPU Forced Escape Laboratory")
print("="*45)
for m in ["Siren", "Glitch"]:
    result = force_escape_test(n_titan, m)
    print(f"System: {m:7} | {result}")