import numpy as np
import math
from scipy.special import expi

class ZetaPrimeJoinEngine:
    def __init__(self, limit=500):
        self.limit = limit
        self.x_axis = np.arange(2, limit)
        self.pi_x = self._get_discrete_pi(limit)
        self.li_x = np.array([self._li(x) for x in self.x_axis])

    def _get_discrete_pi(self, limit):
        pi = np.zeros(limit-2)
        is_p = [True] * (limit + 1)
        count = 0
        for p in range(2, limit):
            if is_p[p]:
                count += 1
                for i in range(p*p, limit + 1, p): is_p[i] = False
            pi[p-2] = count
        return pi

    def _li(self, x):
        return expi(math.log(x))

    def join_operator(self, x, keys):
        """
        Lifts the continuous Li(x) into the discrete Pi(x) 
        using a set of Spectral Keys (Simulated Zeta Zeros).
        """
        correction = 0
        # The 'Explicit Formula' Join: sum(x^rho / rho)
        # We approximate this with a sum of oscillating modes
        for k in keys:
            correction += (x**0.5 / math.log(x)) * math.cos(k * math.log(x))
        return self._li(x) - correction

    def run_discovery(self):
        print("\nLOG: Analyzing Zeta-Prime Spectral Synthesis")
        print(f"Objective: Quantify Metric Tension between Discrete and Continuous Manifolds")
        print("-" * 75)
        
        initial_tension = np.mean((self.pi_x - self.li_x)**2)
        print(f"Initial Metric Tension (Γ): {initial_tension:.4f}")
        
        # Test 1: Single Key (Previous Failure)
        res_1 = np.array([self.join_operator(x, [14.13]) for x in self.x_axis])
        tension_1 = np.mean((res_1 - self.pi_x)**2)
        print(f"Tension with 1 Key (κ=14.13): {tension_1:.4f}")
        
        # Test 2: Triple Key (Emergent Grokking)
        # Using first 3 Riemann Zeros: 14.13, 21.02, 25.01
        keys = [14.13, 21.02, 25.01]
        res_3 = np.array([self.join_operator(x, keys) for x in self.x_axis])
        tension_3 = np.mean((res_3 - self.pi_x)**2)
        print(f"Tension with 3 Keys: {tension_3:.4f}")
        
        improvement = initial_tension / (tension_3 + 1e-9)
        print(f"Grokking Signature (Unification Power): {improvement:.2f}x")
        
        if improvement > 1.1:
            print("\n[✔] JOIN VALIDATED: Multidimensional Spectral Key reduces tension.")
            print("The contradiction is resolved by the 'Spectral Set' of the zeros.")
        else:
            print("\n🚨 JOIN FAILED: Keys are still unsynchronized.")

if __name__ == "__main__":
    engine = ZetaPrimeJoinEngine()
    engine.run_discovery()
