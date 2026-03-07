import numpy as np
import math

class SpectralDimensionCalculator:
    """
    Calculates the Spectral Dimension (D_S) of a logical manifold.
    D_S is derived from the scaling of the eigenvalues of the transition matrix.
    N(lambda) ~ lambda^(D_S/2)
    """
    def __init__(self, n_states=100):
        self.n_states = n_states

    def build_matrix(self, sequence):
        matrix = np.zeros((self.n_states, self.n_states))
        for i in range(len(sequence) - 1):
            matrix[sequence[i] % self.n_states, sequence[i+1] % self.n_states] += 1
        row_sums = matrix.sum(axis=1)
        return np.divide(matrix, row_sums[:, np.newaxis], out=np.zeros_like(matrix), where=row_sums[:, np.newaxis]!=0)

    def calculate_spectral_dimension(self, sequence):
        matrix = self.build_matrix(sequence)
        # We look at the 'Return Probability' P(t) ~ t^(-D_S/2)
        # For a discrete matrix, we use the trace of the powers of the matrix
        # But a simpler proxy is the distribution of eigenvalues near 1.0
        eigenvalues = np.sort(np.abs(np.linalg.eigvals(matrix)))[::-1]
        
        # We look at the decay of the first 10 eigenvalues
        # log(1 - lambda_i) vs log(i)
        significant_evs = eigenvalues[1:11]
        if any(significant_evs >= 1.0): return 0.0
        
        x = np.log(np.arange(1, 11))
        y = np.log(1.0 - significant_evs)
        
        # The slope gives an estimate of the Spectral Dimension
        coeffs = np.polyfit(x, y, 1)
        d_s = abs(coeffs[0]) * 2.0
        return d_s

if __name__ == "__main__":
    calc = SpectralDimensionCalculator(n_states=50)
    
    # 1. 1D-like flow (Sequential)
    seq1 = [i % 50 for i in range(1000)]
    print(f"1D Flow Spectral Dimension: {calc.calculate_spectral_dimension(seq1):.4f}")
    
    # 2. 2D-like flow (Stochastic)
    np.random.seed(42)
    seq2 = np.random.randint(0, 50, 1000)
    print(f"2D Flow Spectral Dimension: {calc.calculate_spectral_dimension(seq2):.4f}")
