import math
import numpy as np

class SingularityDetector:
    """
    GPU Core Tool: Measures the 'Axiomatic Strength' of a logical coordinate.
    A 'Singularity' is defined as a point where algorithmic complexity (S) 
    cannot be dissipated by the current Phase-Locking operators.
    """
    def measure_strength(self, n, axioms):
        # S = 1 - (Max Phase-Lock Potential)
        # If n can be formed by adding existing axioms, its strength is low.
        max_lock = 0
        for a in axioms:
            if a >= n: continue
            if (n - a) in axioms:
                # Binary resonance found
                max_lock = 0.8 # Strong lock
                break
        
        # If no binary lock, check for higher-order resonance
        if max_lock == 0:
            # Slower check for ternary or higher (simplified)
            strength = 1.0 # Pure Singularity
        else:
            strength = 1.0 - max_lock
            
        return strength

    def run_discovery(self, limit=100):
        print("🔭 DISCOVERY PROTOCOL: SINGULARITY EXTRACTION")
        print(f"{'N':<5} | {'Type':<12} | {'Singularity Strength (Σ)'} | {'Implication'}")
        print("-" * 65)
        
        axioms = {2, 3}
        for i in range(4, limit):
            sigma = self.measure_strength(i, axioms)
            is_prime = all(i % p != 0 for p in range(2, int(math.sqrt(i))+1))
            
            if is_prime:
                axioms.add(i)
                label = "PRIME"
                color = "\033[91m"
            else:
                label = "COMPOSITE"
                color = "\033[94m"
                
            if sigma > 0.5:
                impl = "AXIOMATIC BIRTH"
            else:
                impl = "PHASE-LOCKED"
                
            if i % 10 == 0 or is_prime: # Sample output
                print(f"{color}{i:<5} | {label:<12} | {sigma:<24.4f} | {impl}\033[0m")

if __name__ == "__main__":
    SingularityDetector().run_discovery()
