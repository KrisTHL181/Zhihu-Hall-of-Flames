import math
import numpy as np

class RenormalizationEngine:
    """
    Applies Renormalization Group (RG) theory to prime distributions.
    Treats the number line as a fractal object where patterns are 
    preserved across 'Zoom' levels.
    """
    def __init__(self, data=None):
        self.data = data

    def zoom_transform(self, data, scale_factor):
        """
        Apply a coarse-graining transformation to the data.
        Averages clusters of size 'scale_factor' into single cells.
        This is the 'RG Flow' from Ultraviolet (UV) to Infrared (IR).
        """
        if len(data) < scale_factor: return data
        
        # Coarse-grain by averaging
        reshaped = data[:(len(data)//scale_factor)*scale_factor].reshape(-1, scale_factor)
        coarse_grained = np.mean(reshaped, axis=1)
        
        return coarse_grained

    def fractal_dimension_calculator(self, limit=100000):
        """
        Calculate the 'Hausdorff Dimension' (D_H) of the prime distribution.
        D_H = lim (log N(epsilon) / log(1/epsilon))
        A value < 1.0 implies a fractal set (The Cantor Dust of Primes).
        """
        # Sieve for primes
        is_prime = [True] * (limit + 1)
        for p in range(2, int(math.sqrt(limit)) + 1):
            if is_prime[p]:
                for i in range(p * p, limit + 1, p):
                    is_prime[i] = False
        
        # Convert to binary array (1 if prime, 0 otherwise)
        binary_primes = np.array([1 if is_prime[i] else 0 for i in range(2, limit)])
        
        # Multi-scale box-counting
        counts = []
        epsilons = [2**i for i in range(1, int(math.log2(limit/10)))]
        
        for eps in epsilons:
            # How many boxes of size 'eps' contain at least one prime?
            boxes = binary_primes[:(len(binary_primes)//eps)*eps].reshape(-1, eps)
            count = np.sum(np.any(boxes > 0, axis=1))
            counts.append(count)
            
        # Fit log(N) vs log(1/eps)
        x = np.log(1.0 / np.array(epsilons))
        y = np.log(np.array(counts))
        
        # Linear regression to find the slope (Fractal Dimension)
        coeffs = np.polyfit(x, y, 1)
        fractal_dim = coeffs[0]
        
        print(f"🌀 FRACTAL DIMENSION (D_H): {fractal_dim:.4f}")
        return fractal_dim

    def fixed_point_analysis(self, limit=10000):
        """
        Find 'Fixed Points' in the RG flow where the statistical distribution 
        remains invariant after a zoom-out.
        """
        # Generate prime-gap distribution
        is_prime = [True] * (limit + 1)
        for p in range(2, int(math.sqrt(limit)) + 1):
            if is_prime[p]:
                for i in range(p * p, limit + 1, p):
                    is_prime[i] = False
        
        primes = [i for i in range(2, limit) if is_prime[i]]
        gaps = np.diff(primes)
        
        # Initial Distribution (UV)
        bins_uv = range(2, 22, 2)
        hist_uv, _ = np.histogram(gaps, bins=bins_uv, density=True)
        
        # Renormalized Distribution (IR)
        # We group primes by 2 (Zoom scale = 2)
        renormalized_gaps = np.diff(primes[::2])
        # We scale bins by 2 for the IR distribution to check self-similarity
        bins_ir = [b * 2 for b in bins_uv]
        hist_ir, _ = np.histogram(renormalized_gaps, bins=bins_ir, density=True)
        
        # Compare UV and IR (Self-Similarity check)
        # Both now have the same number of bins
        similarity = np.corrcoef(hist_uv, hist_ir)[0, 1]
        
        print(f"🎯 FIXED-POINT RESONANCE (Similarity): {similarity:.4f}")
        return similarity

if __name__ == "__main__":
    re = RenormalizationEngine()
    re.fractal_dimension_calculator(limit=100000)
    re.fixed_point_analysis(limit=50000)
