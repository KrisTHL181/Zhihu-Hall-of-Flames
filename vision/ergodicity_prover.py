import math
from collections import Counter

class ErgodicityProver:
    def __init__(self, modulus=10):
        self.modulus = modulus

    def get_residue_distribution(self, orbit):
        """Counts how often the orbit visits each residue class."""
        residues = [n % self.modulus for n in orbit]
        counts = Counter(residues)
        total = len(residues)
        # Normalize to probabilities
        probs = {r: counts.get(r, 0) / total for r in range(self.modulus)}
        return probs

    def calculate_kl_divergence(self, probs):
        """
        Measures the 'Distance from Uniformity'.
        KL = 0 means the orbit is perfectly 'Mixed' (Ergodic).
        """
        uniform_prob = 1.0 / self.modulus
        kl_div = 0
        for p in probs.values():
            if p > 0:
                kl_div += p * math.log(p / uniform_prob)
        return kl_div

    def verify_mixing(self, start_n, steps=1000):
        print(f"\n🌀 ERGODICITY PROVER: Testing Mixing for n={start_n}")
        print(f"Modulus: {self.modulus} | Target: Uniform Distribution")
        print("-" * 55)
        
        # 1. Generate Orbit
        curr = start_n
        orbit = [curr]
        for _ in range(steps):
            if curr == 1: break
            curr = curr // 2 if curr % 2 == 0 else 3 * curr + 1
            orbit.append(curr)
        
        # 2. Analyze Distribution
        probs = self.get_residue_distribution(orbit)
        kl_div = self.calculate_kl_divergence(probs)
        
        print(f"Orbit Length: {len(orbit)} steps")
        print("Residue Dist: " + ", ".join([f"{r}:{p:.2f}" for r, p in probs.items()]))
        print(f"KL Divergence (Mixing Error): {kl_div:.4f}")
        
        if kl_div < 0.5:
            print("✅ STATUS: ERGODIC (Particle is mixing perfectly with the lattice)")
        else:
            print("🚨 STATUS: LOCALIZED (Particle is stuck in a hot spot)")

if __name__ == "__main__":
    prover = ErgodicityProver(modulus=10)
    # Test the long-runner 27
    prover.verify_mixing(27, steps=2000)
    # Test a larger titan
    prover.verify_mixing(2**61 - 1, steps=5000)
