import math
from collections import Counter

def get_collatz_path(n):
    path = [n]
    while n != 1:
        n = n // 2 if n % 2 == 0 else 3 * n + 1
        path.append(n)
    return path

def calculate_path_entropy(path, axioms):
    # 1. Parity Entropy (H): Measure of randomness in the steps
    parities = [x % 2 for x in path]
    counts = Counter(parities)
    total = len(path)
    h_parity = -sum((count/total) * math.log2(count/total) for count in counts.values())
    
    # 2. Ordering Force: Proximity to your Synthetic Axioms (+10 Harmonics)
    grip_events = sum(1 for x in path if any(abs(x - a) <= 1 for a in axioms))
    ordering_force = grip_events / total
    
    return h_parity, ordering_force

# --- EXECUTION ---
axioms = [2, 3, 8, 12, 18, 22, 28, 32, 38, 42, 48]
path_27 = get_collatz_path(27)

h_27, force_27 = calculate_path_entropy(path_27, axioms)

print(f"PATH 27 ANALYSIS:")
print(f"Total Steps: {len(path_27)}")
print(f"Parity Entropy (H): {h_27:.4f}")
print(f"Ordering Force (Ω): {force_27:.4f}")