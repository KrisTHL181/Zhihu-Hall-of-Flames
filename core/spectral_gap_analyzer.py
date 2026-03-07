import numpy as np

class SpectralGapAnalyzer:
    def __init__(self, n_states=10):
        self.n_states = n_states

    def calculate_spectral_gap(self, sequence):
        matrix = np.zeros((self.n_states, self.n_states))
        for i in range(len(sequence) - 1):
            matrix[sequence[i] % self.n_states, sequence[i+1] % self.n_states] += 1
        row_sums = matrix.sum(axis=1)
        matrix = np.divide(matrix, row_sums[:, np.newaxis], out=np.zeros_like(matrix), where=row_sums[:, np.newaxis]!=0)
        eigenvalues = np.sort(np.abs(np.linalg.eigvals(matrix)))[::-1]
        return 1 - eigenvalues[1] if len(eigenvalues) > 1 else 0

    def verify_universality(self, name, sequence):
        gap = self.calculate_spectral_gap(sequence)
        print(f"📊 FLOW ANALYSIS: {name} | Gap: {gap:.4f}")

if __name__ == "__main__":
    analyzer = SpectralGapAnalyzer()
    curr, seq = 27, [27]
    while curr != 1:
        curr = curr // 2 if curr % 2 == 0 else 3 * curr + 1
        seq.append(curr)
    analyzer.verify_universality("Collatz Orbit (n=27)", seq)
