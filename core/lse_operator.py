import math
import numpy as np

class LSEPhaseEngine:
    def __init__(self, beta=1.0, threshold=0.1):
        """
        beta: The Phase-Locking Coefficient.
              beta -> 0: Multiplication (Geometric Mean)
              beta = 1: Standard Addition
              beta -> inf: Tropical Addition (Max)
        threshold: The 'fuzzy' resonance width of the gas.
        """
        self.beta = beta
        self.threshold = threshold
        self.axioms = [2.0] # Initial Seed
        self.history = []

    def lse_op(self, x, y):
        """The Unified Gaseous Operator: Log-Sum-Exp in Log-Space"""
        # We work in linear space but apply the LSE transformation
        # x (+) y = exp( (1/beta) * ln( exp(beta*ln x) + exp(beta*ln y) ) )
        # Simplified: (x^beta + y^beta)^(1/beta)  -- The Power Mean!
        
        if self.beta == 0: # Limiting case: Geometric Mean
            return math.sqrt(x * y)
        
        try:
            return (x**self.beta + y**self.beta)**(1/self.beta)
        except OverflowError:
            return max(x, y)

    def is_resonant(self, n):
        """Checks if 'n' can be formed by a pairwise 'collision' of axioms."""
        for i in range(len(self.axioms)):
            for j in range(i, len(self.axioms)):
                val = self.lse_op(self.axioms[i], self.axioms[j])
                if abs(n - val) < self.threshold:
                    return True, f"{self.axioms[i]} (+) {self.axioms[j]}"
        return False, None

    def run_simulation(self, limit=30):
        print(f"🌀 SIMULATING LSE UNIVERSE (beta={self.beta})")
        print(f"{'N':<5} | {'STATE':<18} | {'RESONANCE / VALUE'}")
        print("-" * 50)
        
        for n in range(3, limit + 1):
            n_float = float(n)
            resonant, detail = self.is_resonant(n_float)
            
            if resonant:
                state = "LOCKED"
                print(f"{n:<5} | {state:<18} | {detail}")
            else:
                state = "AXIOM_BIRTH"
                self.axioms.append(n_float)
                # Use red for axioms
                print(f"\033[91m{n:<5} | {state:<18} | NEW SINGULARITY\033[0m")

if __name__ == "__main__":
    # 1. Hot/Superfluid Universe: beta -> 0 (Multiplication-like)
    # Primes here are the standard multiplicative primes.
    hot_engine = LSEPhaseEngine(beta=0.001)
    hot_engine.run_simulation(limit=20)
    
    # 2. Arithmetic Universe: beta = 1.0 (Standard Addition)
    # Axioms here are the 'Goldbach' seeds.
    std_engine = LSEPhaseEngine(beta=1.0)
    std_engine.run_simulation(limit=20)
    
    # 3. Crystalline Universe: beta = 10.0 (Tropical/Max)
    # Addition becomes 'Selection'. Almost everything is an Axiom.
    cold_engine = LSEPhaseEngine(beta=10.0)
    cold_engine.run_simulation(limit=20)
