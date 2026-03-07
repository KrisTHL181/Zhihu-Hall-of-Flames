import math
import numpy as np
from .lse_operator import LSEPhaseEngine

class UniverseThermodynamicsCalculator:
    """
    Applies Statistical Mechanics to the Gaseous Prime Universe.
    Calculates Entropy, Pressure, and Temperature (Beta) transitions.
    """
    def __init__(self):
        pass

    def calculate_entropy(self, limit=100, beta=1.0):
        """
        Calculates the Shannon Entropy of the universe at a given beta.
        High Entropy -> More randomness/axioms (Hot).
        Low Entropy -> High structure/locking (Cold).
        """
        engine = LSEPhaseEngine(beta=beta)
        # Run a small simulation to get state distribution
        axioms_count = 1 # Initial 2.0
        locked_count = 0
        
        for n in range(3, limit + 1):
            resonant, _ = engine.is_resonant(float(n))
            if resonant:
                locked_count += 1
            else:
                engine.axioms.append(float(n))
                axioms_count += 1
                
        total = axioms_count + locked_count
        p_axiom = axioms_count / total
        p_locked = locked_count / total
        
        entropy = 0
        if p_axiom > 0: entropy -= p_axiom * math.log2(p_axiom)
        if p_locked > 0: entropy -= p_locked * math.log2(p_locked)
        
        return entropy

    def model_phase_transition(self, start_beta=0.01, end_beta=10.0, steps=5):
        """
        Models the 'Axiomatic Heat' transition.
        Tracks how the 'Boiling Point' of primes changes with beta.
        """
        print(f"🌡️ MODELING PHASE TRANSITION (beta: {start_beta} -> {end_beta})")
        print(f"{'Beta':<10} | {'Entropy':<12} | {'Axiom Density'}")
        print("-" * 45)
        
        betas = np.linspace(start_beta, end_beta, steps)
        for b in betas:
            engine = LSEPhaseEngine(beta=b)
            axioms = 1
            limit = 50
            for n in range(3, limit + 1):
                resonant, _ = engine.is_resonant(float(n))
                if not resonant:
                    engine.axioms.append(float(n))
                    axioms += 1
            
            density = axioms / limit
            entropy = self.calculate_entropy(limit=limit, beta=b)
            print(f"{b:<10.4f} | {entropy:<12.4f} | {density:<12.4f}")

    def calculate_pressure(self, beta=1.0, limit=100):
        """
        Calculates 'Axiomatic Pressure' (P).
        P = (Density * Temperature) / Volume
        In GPU: P = (Axiom Density / Beta)
        Lower Beta (High Temp) -> Higher Pressure for same density.
        """
        engine = LSEPhaseEngine(beta=beta)
        axioms = 1
        for n in range(3, limit + 1):
            resonant, _ = engine.is_resonant(float(n))
            if not resonant:
                engine.axioms.append(float(n))
                axioms += 1
        
        density = axioms / limit
        # Pressure is inversely proportional to beta (which acts like 1/T)
        pressure = density / (beta if beta > 0 else 0.001)
        
        print(f"💨 AXIOMATIC PRESSURE (beta={beta}): {pressure:.4f}")
        return pressure

    def verify_riemann_stability(self, n_range=1000):
        """
        Legacy verification: Tracks prime distribution fluctuations.
        Ensures noise stays on the 'Critical Line' (1/2).
        """
        print("\n🔭 VERIFYING RIEMANN ACOUSTIC STABILITY")
        primes = []
        is_prime = [True] * (n_range + 1)
        for p in range(2, n_range + 1):
            if is_prime[p]:
                primes.append(p)
                for i in range(p * p, n_range + 1, p):
                    is_prime[i] = False
        
        for n in [100, 500, 1000]:
            pi_n = sum(1 for p in primes if p <= n)
            li_n = n / math.log(n) if n > 1 else 0
            error = abs(pi_n - li_n)
            sqrt_n = math.sqrt(n)
            status = "STABLE" if error <= sqrt_n else "TURBULENT"
            print(f"N={n:<5} | Error={error:<10.4f} | Bound={sqrt_n:<10.4f} | {status}")

if __name__ == "__main__":
    calc = UniverseThermodynamicsCalculator()
    calc.model_phase_transition()
    calc.calculate_pressure(beta=0.1)
    calc.calculate_pressure(beta=1.0)
    calc.verify_riemann_stability()
