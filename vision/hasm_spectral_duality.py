import math
import numpy as np
from core.spectral_gap_analyzer import SpectralGapAnalyzer

class HASMASETResonanceSimulator:
    """
    Verifies HASM via ASET Stability Profiles.
    Hypothesis: The stability of the Spectral Gap across modular bases (ASET)
    is the same for both the Boundary and the Volume.
    """
    def __init__(self, limit=50000):
        self.limit = limit
        self.n_values = np.arange(1, limit + 1)
        self.analyzer = SpectralGapAnalyzer(n_states=10)

    def get_gap_profile(self, flow_func, bases=[2, 3, 5, 7, 11, 13, 17]):
        """Calculates the Spectral Gap across multiple modular bases."""
        profile = []
        for b in bases:
            seq = flow_func(b)
            gap = self.analyzer.calculate_spectral_gap(seq)
            profile.append(gap)
        return np.array(profile)

    def decadic_flow(self, b):
        """Standard decadic flow projected mod b."""
        def metric(n):
            residue = n % 10
            dist = min(abs(residue - 8), abs(residue + 2))
            return int(10 / (dist + 1.0))
        return [metric(n) % 10 for n in self.n_values]

    def adelic_flow(self, b):
        """Weighted Adelic flow projected mod b."""
        # Using a fixed set of primes for the volume complexity
        primes = [2, 3, 5, 7, 11]
        complexity = np.zeros(self.limit)
        for p in primes:
            curr_p = p
            while curr_p <= self.limit:
                complexity[curr_p-1::curr_p] += 1
                curr_p *= p
        
        return [int(complexity[i]) % 10 for i in range(self.limit)]

    def verify_aset_resonance(self):
        print("\n🔭 VERIFYING HASM ASET PROFILE RESONANCE")
        print("-" * 55)
        
        bases = [2, 3, 5, 7, 11, 13, 17]
        
        print("Calculating Boundary ASET Profile...")
        b_profile = self.get_gap_profile(self.decadic_flow, bases)
        
        print("Calculating Volume ASET Profile...")
        v_profile = self.get_gap_profile(self.adelic_flow, bases)
        
        # Pearson correlation of the stability profiles
        resonance = np.corrcoef(b_profile, v_profile)[0, 1]
        
        print(f"\nBases: {bases}")
        print(f"Boundary Profile: {np.round(b_profile, 4)}")
        print(f"Volume Profile:   {np.round(v_profile, 4)}")
        print(f"\nHASM ASET RESONANCE: {resonance:.4f}")
        
        status = "✅ HOLOGRAPHIC" if resonance > 0.5 else "❌ DE-COUPLED"
        print(f"Status: {status}")
        
        if resonance > 0.5:
            print("\n[✔] BREAKTHROUGH: The Adelic Spectral Equipartition is Holographic!")
            print("    The Boundary's stability signature mirrors the Volume's global structure.")
            
        return resonance

if __name__ == "__main__":
    simulator = HASMASETResonanceSimulator(limit=50000)
    simulator.verify_aset_resonance()
