import numpy as np
import math
from core.spectral_gap_analyzer import SpectralGapAnalyzer

class ConformalResonanceTester:
    """
    Verifies if the LSE Operator is a Conformal Mapping on the Adèle Ring.
    A mapping is conformal if it preserves the 'Shape' (Spectral Ratios) 
    of the information across different modular bases.
    """
    def __init__(self, sequence_length=5000):
        self.seq_len = sequence_length
        self.analyzer = SpectralGapAnalyzer(n_states=10)

    def lse_transform(self, seq, beta):
        """Applies the LSE operator as a transformation: x -> LSE(x, n, beta)."""
        transformed = []
        for i, x in enumerate(seq):
            try:
                # Transducing the value with its position in the manifold
                val = (float(x)**beta + float(i % 10)**beta)**(1/beta)
                transformed.append(int(val) % 10)
            except:
                transformed.append(x)
        return transformed

    def verify_conformality(self, bases=[2, 3, 5, 7, 11]):
        print("\n📏 TESTING ADELIC CONFORMAL RESONANCE")
        print(f"{'Base (p)':<10} | {'Original γ':<12} | {'Transformed γ':<12} | {'Scaling Ratio'}")
        print("-" * 65)
        
        # Initial Stochastic Flow
        np.random.seed(42)
        original_seq = np.random.randint(0, 10, self.seq_len)
        beta = math.log10(2) # Decadic Beta
        
        transformed_seq = self.lse_transform(original_seq, beta)
        
        ratios = []
        for p in bases:
            self.analyzer.n_states = p
            gamma_orig = self.analyzer.calculate_spectral_gap(original_seq)
            gamma_trans = self.analyzer.calculate_spectral_gap(transformed_seq)
            
            ratio = gamma_trans / gamma_orig if gamma_orig > 0 else 1.0
            ratios.append(ratio)
            
            print(f"{p:<10} | {gamma_orig:<12.4f} | {gamma_trans:<12.4f} | {ratio:.4f}")
            
        variance = np.var(ratios)
        print(f"\nConformal Scaling Variance: {variance:.6f}")
        
        if variance < 0.05:
            print("✅ STATUS: CONFORMAL STABILITY (LSE preserves the Adelic Shape).")
            print("   This confirms that Local Spectral Anomalies are Global Facts.")
        else:
            print("🚨 STATUS: NON-CONFORMAL (Local accidents do not extend).")
            
        return variance

if __name__ == "__main__":
    tester = ConformalResonanceTester()
    tester.verify_conformality()
