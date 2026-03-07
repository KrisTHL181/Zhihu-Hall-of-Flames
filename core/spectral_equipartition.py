import numpy as np
import math

class SpectralEquipartitionAnalyzer:
    """
    Analyzes the 'Adelic Equipartition' of Spectral Gaps.
    Hypothesis: The Mixing Rate (gamma) of a logical flow is invariant
    across different modular bases (profinite completions).
    """
    def __init__(self, sequence):
        self.sequence = sequence

    def calculate_spectral_gap(self, modulus):
        """Builds a transition matrix mod 'modulus' and returns the gap."""
        matrix = np.zeros((modulus, modulus))
        for i in range(len(self.sequence) - 1):
            s_from = self.sequence[i] % modulus
            s_to = self.sequence[i+1] % modulus
            matrix[s_from, s_to] += 1
        
        # Row-normalize
        row_sums = matrix.sum(axis=1)
        matrix = np.divide(matrix, row_sums[:, np.newaxis], out=np.zeros_like(matrix), where=row_sums[:, np.newaxis]!=0)
        
        # Eigenvalues
        try:
            eigenvalues = np.linalg.eigvals(matrix)
            abs_eigenvalues = np.sort(np.abs(eigenvalues))[::-1]
            if len(abs_eigenvalues) < 2: return 0
            # lambda_1 is always 1.0 for a stochastic matrix
            lambda_2 = abs_eigenvalues[1]
            return 1 - lambda_2
        except:
            return 0

    def verify_equipartition(self, name, bases=[2, 3, 5, 7, 10, 11]):
        print(f"\n⚖️ ANALYZING ADELIC SPECTRAL EQUIPARTITION: {name}")
        print(f"{'Base (p)':<10} | {'Spectral Gap (γ)':<20} | {'Variance from Mean'}")
        print("-" * 60)
        
        gaps = []
        for b in bases:
            gap = self.calculate_spectral_gap(b)
            gaps.append(gap)
            
        avg_gap = np.mean(gaps)
        for i, b in enumerate(bases):
            diff = gaps[i] - avg_gap
            print(f"{b:<10} | {gaps[i]:<20.4f} | {diff:+.4f}")
            
        var = np.var(gaps)
        print(f"\nGlobal Equipartition Variance: {var:.6f}")
        if var < 0.05:
            print("✅ STATUS: ADELIC STABILITY (Information is distributed evenly).")
        else:
            print("🚨 STATUS: ANISOTROPIC FLOW (Potential Logic Leakage).")

if __name__ == "__main__":
    # Test on Collatz sequence (n=27)
    curr, seq = 27, [27]
    for _ in range(5000):
        curr = curr // 2 if curr % 2 == 0 else 3 * curr + 1
        seq.append(curr)
        if curr == 1: break
        
    analyzer = SpectralEquipartitionAnalyzer(seq)
    analyzer.verify_equipartition("Collatz Orbit (n=27)")
    
    # Test on Prime Gaps
    def get_primes(n):
        primes, is_p = [], [True]*(n+1)
        for p in range(2, n+1):
            if is_p[p]:
                primes.append(p)
                for i in range(p*p, n+1, p): is_p[i] = False
        return primes
    primes = get_primes(5000)
    gaps = [primes[i+1] - primes[i] for i in range(len(primes)-1)]
    
    gap_analyzer = SpectralEquipartitionAnalyzer(gaps)
    gap_analyzer.verify_equipartition("Prime Gap Sequence")
