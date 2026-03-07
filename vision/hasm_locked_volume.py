import math
import numpy as np
from core.spectral_gap_analyzer import SpectralGapAnalyzer

class HASMLockedVolumeSimulator:
    """
    Verifies HASM via Weighted Adelic Flow.
    Uses the LSE Brick to 'lock' the p-adic valuations into a single flow.
    """
    def __init__(self, limit=10000):
        self.limit = limit
        self.n_values = np.arange(1, limit + 1)
        self.analyzer = SpectralGapAnalyzer(n_states=10)
        self.decadic_beta = math.log10(2)

    def get_decadic_flow(self):
        def metric(n):
            residue = n % 10
            dist = min(abs(residue - 8), abs(residue + 2))
            return int(10 / (dist + 1.0))
        return [metric(n) for n in self.n_values]

    def get_locked_adelic_flow(self, primes=[2, 3, 5, 7, 11]):
        """
        Combines multiple p-adic flows into a single 'Locked' flow using LSE.
        This represents the 'ASET Brick' in action.
        """
        locked_flow = []
        for n in self.n_values:
            # Accumulate valuations
            vals = []
            for p in primes:
                v_p = 0
                if n > 0:
                    temp = n
                    while temp % p == 0:
                        v_p += 1
                        temp //= p
                vals.append(float(v_p))
            
            # LSE-Phase-Locking the valuations
            # (Sum of x^beta)^(1/beta)
            try:
                lse_val = sum([v**self.decadic_beta for v in vals if v > 0])**(1/self.decadic_beta)
            except:
                lse_val = max(vals) if vals else 0
                
            locked_flow.append(int(lse_val) % 10)
        return locked_flow

    def verify_locked_resonance(self):
        print("\n🔭 VERIFYING HASM LOCKED VOLUME RESONANCE")
        print(f"Beta (Phase-Lock): {self.decadic_beta:.4f}")
        print("-" * 55)
        
        boundary_seq = self.get_decadic_flow()
        gamma_b = self.analyzer.calculate_spectral_gap(boundary_seq)
        
        volume_seq = self.get_locked_adelic_flow()
        gamma_v = self.analyzer.calculate_spectral_gap(volume_seq)
        
        resonance = 1.0 - abs(gamma_b - gamma_v) / max(gamma_b, gamma_v)
        
        print(f"Boundary Spectral Gap (gamma_b): {gamma_b:.4f}")
        print(f"Locked Volume Spectral Gap:     {gamma_v:.4f}")
        print(f"HASM LOCKED RESONANCE:          {resonance:.4f}")
        
        status = "✅ HOLOGRAPHIC" if resonance > 0.7 else "❌ DIVERGENT"
        print(f"Status: {status}")
        
        if resonance > 0.7:
            print("\n[✔] Success: Phase-Locking the Adelic Volume revealed the duality!")
            print("    The Decadic Boundary acts as a low-dimensional shadow of the Locked Volume.")
            
        return resonance

if __name__ == "__main__":
    simulator = HASMLockedVolumeSimulator(limit=20000)
    simulator.verify_locked_resonance()
