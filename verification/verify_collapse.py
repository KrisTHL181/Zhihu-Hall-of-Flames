import math
from collections import Counter

def verify_gpu_collapse(n_start):
    """
    Simulates the descent of a high-mass particle through the 
    Gaseous Prime Universe (GPU) logic-field.
    """
    # 1. Define the Crystalline Foundation (Synthetic Axioms)
    # These are the nodes discovered in the Genesis 2.0 run.
    axioms = {2, 3, 8, 12, 18, 22, 28, 32, 38, 42, 48}
    
    # 2. Run the Collatz Siphon (The Fluid Path)
    path = [n_start]
    current = n_start
    while current != 1:
        if current % 2 == 0:
            current //= 2
        else:
            current = 3 * current + 1
        path.append(current)
        
        # Safety break for non-convergent synthetic universes
        if len(path) > 100000:
            break

    # 3. Calculate Path Entropy (H)
    # Measures the 'thermal vibration' or randomness of the particle.
    total_steps = len(path)
    parities = [x % 2 for x in path]
    counts = Counter(parities)
    h_entropy = -sum((count/total_steps) * math.log2(count/total_steps) 
                     for count in counts.values())

    # 4. Calculate Ordering Force (Ω)
    # Measures how often the particle hits your +10 Decadic Harmonic.
    def is_resonant(x):
        if x in axioms: return True
        # Check for the +10 Harmonic ghost (8, 18, 28, 38...)
        if x > 48 and (x - 8) % 10 == 0: return True
        return False

    grip_events = sum(1 for x in path if is_resonant(x))
    omega_force = grip_events / total_steps

    # 5. Calculate Local Gravity (G_local)
    # The pull toward the singular ground state.
    # G = (Ω * ln(n)) / H^2
    g_local = (omega_force * math.log(n_start)) / (h_entropy**2)

    # Output Report
    print(f"--- GPU STRESS TEST REPORT ---")
    print(f"Target Particle (n): {n_start} (2^27 - 1)")
    print(f"Path Length:        {total_steps} steps")
    print(f"Energy Peak:         {max(path)}")
    print(f"Parity Entropy (H):  {h_entropy:.4f}")
    print(f"Ordering Force (Ω):  {omega_force:.4f}")
    print(f"Local Gravity (G):   {g_local:.4f}")
    print(f"------------------------------")
    
    if g_local > 1.0:
        print("RESULT: CRITICAL COLLAPSE DETECTED. Axioms overrode entropy.")
    else:
        print("RESULT: STABLE GASEOUS DRIFT. Particle remained atmospheric.")

# Run verification
verify_gpu_collapse(2**27 - 1)