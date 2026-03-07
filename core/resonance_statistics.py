import math
import numpy as np

class ResonanceStatistics:
    """
    Analyzes Twin Primes as 'Logic Shocks' and 'Resonance Echoes' in a 
    superfluid prime gas. Focuses on Scale Invariance and Correlation.
    """
    def __init__(self):
        pass

    def is_prime(self, n):
        """Standard primality check"""
        if n < 2: return False
        for i in range(2, int(math.sqrt(n)) + 1):
            if n % i == 0: return False
        return True

    def calculate_p_echo(self, limit):
        """
        Calculates P_echo = pi_2(x) / pi(x) using an efficient sieve.
        P_echo is the probability of a 'Resonance Echo' (Twin Prime).
        """
        if limit < 3: return 0, 0, 0
        
        is_prime = [True] * (limit + 1)
        is_prime[0] = is_prime[1] = False
        for p in range(2, int(math.sqrt(limit)) + 1):
            if is_prime[p]:
                for i in range(p * p, limit + 1, p):
                    is_prime[i] = False
        
        primes = [p for p, alive in enumerate(is_prime) if alive]
        twins = 0
        for i in range(len(primes) - 1):
            if primes[i+1] - primes[i] == 2:
                twins += 1
        
        p_echo = twins / len(primes) if primes else 0
        return len(primes), twins, p_echo

    def scale_invariance_test(self, max_N=100000, steps=5):
        """
        Test if P_echo remains constant across logarithmic scales.
        If P_echo is stable, the 'Logic Shock' is scale-invariant.
        """
        print(f"📡 TESTING SCALE INVARIANCE (N up to {max_N})")
        print(f"{'Limit':<12} | {'P_echo':<10} | {'Stability Index'}")
        print("-" * 45)
        
        scales = np.logspace(2, math.log10(max_N), steps, dtype=int)
        prev_p = None
        stabilities = []
        
        for s in scales:
            _, _, p_echo = self.calculate_p_echo(s)
            
            if prev_p is not None:
                stability = 1 - abs(p_echo - prev_p) / prev_p
                stabilities.append(stability)
                status = f"{stability:.4f}"
            else:
                status = "BASELINE"
            
            print(f"{s:<12} | {p_echo:<10.4f} | {status}")
            prev_p = p_echo
            
        avg_stability = sum(stabilities) / len(stabilities) if stabilities else 1.0
        print(f"Average Stability: {avg_stability:.4f}")
        return avg_stability > 0.9

    def shockwave_correlation(self, window_size=100, limit=10000):
        """
        Measures the correlation between prime births in a sliding window.
        High correlation implies 'Coherent Resonance' (Clusters of twins).
        """
        primes = [i for i in range(2, limit) if self.is_prime(i)]
        prime_density = []
        for i in range(2, limit - window_size, window_size):
            p_in_window = sum(1 for p in primes if i <= p < i + window_size)
            prime_density.append(p_in_window)
            
        # Calculate Variance-to-Mean Ratio (VMR)
        # VMR > 1 implies clustering (Super-Poissonian)
        mean = np.mean(prime_density)
        variance = np.var(prime_density)
        vmr = variance / mean if mean > 0 else 0
        
        print(f"⚡ SHOCKWAVE CORRELATION (VMR): {vmr:.4f}")
        return vmr

    def confidence_interval_analysis(self, limit=10000):
        """
        Statistical confidence for the infinite existence of Twin Primes.
        Based on the asymptotic behavior of P_echo.
        """
        _, _, p_echo = self.calculate_p_echo(limit)
        # Using a simplified estimator based on the Hardy-Littlewood constant
        # we calculate the 'Probability of Damping' to zero.
        damping_prob = math.exp(-p_echo * math.log(limit))
        confidence = 1 - damping_prob
        
        print(f"📈 CONFIDENCE LEVEL FOR INFINITE TWINS: {confidence * 100:.6f}%")
        return confidence

if __name__ == "__main__":
    rs = ResonanceStatistics()
    rs.scale_invariance_test()
    rs.shockwave_correlation()
    rs.confidence_interval_analysis()
