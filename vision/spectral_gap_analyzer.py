import numpy as np
import math

class SpectralGapAnalyzer:
    def __init__(self, n_states=100):
        self.n_states = n_states

    def build_transition_matrix(self, sequence):
        """
        Builds a Markov Transition Matrix for any logical flow.
        Maps the probability of moving from state i to state j.
        """
        matrix = np.zeros((self.n_states, self.n_states))
        for i in range(len(sequence) - 1):
            s_from = sequence[i] % self.n_states
            s_to = sequence[i+1] % self.n_states
            matrix[s_from, s_to] += 1
        
        # Normalize rows to sum to 1
        row_sums = matrix.sum(axis=1)
        # Avoid division by zero
        matrix = np.divide(matrix, row_sums[:, np.newaxis], out=np.zeros_like(matrix), where=row_sums[:, np.newaxis]!=0)
        return matrix

    def calculate_spectral_gap(self, matrix):
        """
        The Spectral Gap (1 - lambda_2).
        Gap > 0 means the system is Ergodic and Mixes exponentially fast.
        """
        eigenvalues = np.linalg.eigvals(matrix)
        abs_eigenvalues = np.sort(np.abs(eigenvalues))[::-1]
        
        if len(abs_eigenvalues) < 2: return 0
        # lambda_1 is always 1.0 for a stochastic matrix
        lambda_2 = abs_eigenvalues[1]
        return 1 - lambda_2

    def verify_universality(self, name, sequence):
        matrix = self.build_transition_matrix(sequence)
        gap = self.calculate_spectral_gap(matrix)
        print(f"📊 FLOW ANALYSIS: {name}")
        print(f"Mixing Rate (Spectral Gap): {gap:.4f}")
        status = "ERGODIC (Stable Equilibrium)" if gap > 0.05 else "LOCALIZED (Meta-stable)"
        print(f"Status: {status}\n")
        return gap

if __name__ == "__main__":
    analyzer = SpectralGapAnalyzer(n_states=10)
    
    # 1. Flow A: Collatz (The Descent)
    curr, collatz_seq = 27, [27]
    for _ in range(5000):
        curr = curr // 2 if curr % 2 == 0 else 3 * curr + 1
        collatz_seq.append(curr)
        if curr == 1: break
    analyzer.verify_universality("Collatz Orbit (n=27)", collatz_seq)

    # 2. Flow B: Prime Gaps (The Acoustic Noise)
    def get_primes(n):
        primes, is_p = [], [True]*(n+1)
        for p in range(2, n+1):
            if is_p[p]:
                primes.append(p)
                for i in range(p*p, n+1, p): is_p[i] = False
        return primes
    primes = get_primes(10000)
    gaps = [primes[i+1] - primes[i] for i in range(len(primes)-1)]
    analyzer.verify_universality("Prime Gap Sequence", gaps)

    # 3. Flow C: LSE-Drift (The Theta-Link)
    # Simulating the drift of a value as Beta fluctuates
    lse_drift = [int((10**b + 11**b)**(1/b)) for b in np.linspace(1, 0.1, 1000)]
    analyzer.verify_universality("LSE Indeterminacy Flow", lse_drift)
