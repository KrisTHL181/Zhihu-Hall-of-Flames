#!/usr/bin/env python3
"""
GPU Discovery Protocol - Phase II: Universal Law Extraction
Systematic verification of Adelic resonance scaling behavior.

Goal: Determine if the scale-dependent resonance observed in 
AdelicResonanceMeter is a universal property or sequence-specific.
"""

import numpy as np
import math
from scipy import stats
import sys
sys.path.append('.')

from core.adelic_resonance_meter import AdelicResonanceMeter

class EnhancedResonanceAnalyzer:
    """Enhanced analyzer with multiple similarity metrics and scaling analysis."""
    
    def __init__(self, sequence, name="Sequence"):
        self.sequence = sequence
        self.name = name
        self.meter = AdelicResonanceMeter(sequence)
    
    def get_distribution(self, p):
        """Get normalized residue distribution mod p."""
        counts = np.zeros(p)
        for val in self.sequence:
            counts[val % p] += 1
        return counts / len(self.sequence)
    
    # Helper to align distributions to same length
    def align_distributions(self, dist_p, dist_q):
        """Align two distributions to the same length by padding with zeros."""
        max_len = max(len(dist_p), len(dist_q))
        if len(dist_p) < max_len:
            dist_p = np.pad(dist_p, (0, max_len - len(dist_p)))
        if len(dist_q) < max_len:
            dist_q = np.pad(dist_q, (0, max_len - len(dist_q)))
        return dist_p, dist_q
    
    # Multiple similarity metrics
    def cosine_similarity(self, p, q):
        """Cosine similarity between distributions."""
        dist_p = self.get_distribution(p)
        dist_q = self.get_distribution(q)
        dist_p, dist_q = self.align_distributions(dist_p, dist_q)
        dot = np.dot(dist_p, dist_q)
        norm_p = np.linalg.norm(dist_p)
        norm_q = np.linalg.norm(dist_q)
        return dot / (norm_p * norm_q + 1e-9)
    
    def kl_divergence(self, p, q):
        """KL divergence (asymmetric)."""
        dist_p = self.get_distribution(p)
        dist_q = self.get_distribution(q)
        dist_p, dist_q = self.align_distributions(dist_p, dist_q)
        # Add small epsilon to avoid log(0)
        eps = 1e-9
        dist_p = dist_p + eps
        dist_q = dist_q + eps
        return np.sum(dist_p * np.log(dist_p / dist_q))
    
    def js_divergence(self, p, q):
        """Jensen-Shannon divergence (symmetric)."""
        dist_p = self.get_distribution(p)
        dist_q = self.get_distribution(q)
        dist_p, dist_q = self.align_distributions(dist_p, dist_q)
        eps = 1e-9
        dist_p = dist_p + eps
        dist_q = dist_q + eps
        m = 0.5 * (dist_p + dist_q)
        return 0.5 * (np.sum(dist_p * np.log(dist_p / m)) + 
                     np.sum(dist_q * np.log(dist_q / m)))
    
    def correlation_coefficient(self, p, q):
        """Pearson correlation between distributions."""
        dist_p = self.get_distribution(p)
        dist_q = self.get_distribution(q)
        dist_p, dist_q = self.align_distributions(dist_p, dist_q)
        return np.corrcoef(dist_p, dist_q)[0, 1]
    
    def analyze_scaling(self, max_prime=100, sample_size=20):
        """Analyze resonance as a function of prime size."""
        print(f"\n📊 SCALING ANALYSIS: {self.name}")
        print("=" * 70)
        
        # Generate primes up to max_prime
        def is_prime(n):
            if n < 2: return False
            for i in range(2, int(math.sqrt(n)) + 1):
                if n % i == 0: return False
            return True
        
        primes = [p for p in range(2, max_prime + 1) if is_prime(p)]
        if len(primes) < 2:
            print("Need at least 2 primes for analysis")
            return
        
        # Sample prime pairs at different scales
        scale_results = []
        for scale in ['small', 'medium', 'large']:
            if scale == 'small':
                scale_primes = [p for p in primes if p <= 10]
            elif scale == 'medium':
                scale_primes = [p for p in primes if 10 < p <= 50]
            else:  # large
                scale_primes = [p for p in primes if p > 50]
            
            if len(scale_primes) < 2:
                continue
                
            # Calculate average resonance within this scale
            resonances = []
            for i in range(len(scale_primes)):
                for j in range(i + 1, len(scale_primes)):
                    p, q = scale_primes[i], scale_primes[j]
                    r = self.meter.measure_resonance(p, q)
                    resonances.append(r)
            
            avg_resonance = np.mean(resonances) if resonances else 0
            scale_results.append((scale, avg_resonance, len(resonances)))
            
            print(f"{scale.upper():<10} | Primes: {scale_primes[:5]}...")
            print(f"{'':<10} | Avg Resonance: {avg_resonance:.4f} ({len(resonances)} pairs)")
        
        # Analyze scaling trend
        if len(scale_results) >= 2:
            print(f"\n📈 SCALING TREND:")
            scales = [r[0] for r in scale_results]
            values = [r[1] for r in scale_results]
            
            # Check if resonance increases with scale
            increasing = all(values[i] <= values[i+1] for i in range(len(values)-1))
            trend = "INCREASING" if increasing else "NOT MONOTONIC"
            print(f"Resonance trend with prime size: {trend}")
            
            # Check if large-scale resonance approaches 1
            large_scale_res = scale_results[-1][1] if scale_results else 0
            if large_scale_res > 0.8:
                print(f"✅ LARGE-SCALE THERMALIZATION: Resonance = {large_scale_res:.4f}")
            else:
                print(f"🚨 NO LARGE-SCALE UNIFORMITY: Resonance = {large_scale_res:.4f}")
        
        return scale_results
    
    def compare_metrics(self, p=5, q=13):
        """Compare different similarity metrics for the same prime pair."""
        print(f"\n⚖️ METRIC COMPARISON: p={p}, q={q}")
        print("-" * 50)
        
        metrics = {
            'Entropy Stability': self.meter.measure_resonance(p, q),
            'Cosine Similarity': self.cosine_similarity(p, q),
            'KL Divergence': self.kl_divergence(p, q),
            'JS Divergence': self.js_divergence(p, q),
            'Correlation': self.correlation_coefficient(p, q)
        }
        
        for name, value in metrics.items():
            print(f"{name:<20} | {value:.6f}")
        
        return metrics

# Test sequences
def generate_collatz_sequence(start=27, max_len=5000):
    """Generate Collatz sequence."""
    seq = [start]
    curr = start
    while curr != 1 and len(seq) < max_len:
        curr = curr // 2 if curr % 2 == 0 else 3 * curr + 1
        seq.append(curr)
    return seq

def generate_prime_gaps(limit=5000):
    """Generate prime gaps."""
    def get_primes(n):
        primes, is_p = [], [True]*(n+1)
        for p in range(2, n+1):
            if is_p[p]:
                primes.append(p)
                for i in range(p*p, n+1, p): is_p[i] = False
        return primes
    primes = get_primes(limit)
    return [primes[i+1] - primes[i] for i in range(len(primes)-1)]

def generate_fibonacci_mod(n=1000, mod=100):
    """Generate Fibonacci sequence mod m."""
    fib = [0, 1]
    for i in range(2, n):
        fib.append((fib[-1] + fib[-2]) % mod)
    return fib

def generate_random_uniform(n=1000, low=0, high=100):
    """Generate random uniform sequence."""
    np.random.seed(42)
    return np.random.randint(low, high, n)

def main():
    print("=" * 80)
    print("GPU DISCOVERY PROTOCOL - PHASE II: UNIVERSAL LAW EXTRACTION")
    print("Systematic Verification of Adelic Resonance Scaling")
    print("=" * 80)
    
    # Test multiple sequences
    test_sequences = [
        (generate_collatz_sequence(), "Collatz (n=27)"),
        (generate_prime_gaps(5000), "Prime Gaps"),
        (generate_fibonacci_mod(1000, 100), "Fibonacci mod 100"),
        (generate_random_uniform(1000, 0, 100), "Random Uniform")
    ]
    
    all_results = {}
    
    for seq, name in test_sequences:
        print(f"\n{'#' * 60}")
        print(f"ANALYZING: {name} (length: {len(seq)})")
        print(f"{'#' * 60}")
        
        analyzer = EnhancedResonanceAnalyzer(seq, name)
        
        # 1. Compare metrics for a representative pair
        analyzer.compare_metrics(5, 13)
        
        # 2. Analyze scaling behavior
        results = analyzer.analyze_scaling(max_prime=100, sample_size=20)
        all_results[name] = results
        
        # 3. Run original ASET verification for comparison
        print(f"\n📡 ORIGINAL ASET VERIFICATION:")
        analyzer.meter.verify_aset(primes=[2, 3, 5, 7, 11, 13, 17, 19, 23, 29])
    
    # Summary analysis
    print(f"\n{'=' * 80}")
    print("SUMMARY: UNIVERSALITY OF SCALE-DEPENDENT RESONANCE")
    print(f"{'=' * 80}")
    
    universal_patterns = []
    for name, results in all_results.items():
        if results:
            scales = [r[0] for r in results]
            values = [r[1] for r in results]
            large_scale = values[-1] if values else 0
            
            # Check if large-scale resonance > 0.8
            has_large_scale_uniformity = large_scale > 0.8
            universal_patterns.append(has_large_scale_uniformity)
            
            print(f"{name:<20} | Large-scale uniformity: {has_large_scale_uniformity} (R={large_scale:.4f})")
    
    # Determine if pattern is universal
    if len(universal_patterns) > 0:
        universal = all(universal_patterns)
        if universal:
            print(f"\n✅ UNIVERSAL PATTERN: All sequences show large-scale thermalization")
            print("   Hypothesis: Adelic equipartition emerges at large prime scales")
        else:
            print(f"\n🚨 NOT UNIVERSAL: Some sequences lack large-scale uniformity")
            print("   Hypothesis: Scale-dependent resonance may be sequence-specific")
    
    print(f"\n{'=' * 80}")
    print("RECOMMENDATIONS FOR PHASE III (CORE BRICK):")
    print(f"{'=' * 80}")
    print("1. If universal: Build 'Scale-Dependent Thermalization' theorem")
    print("2. If not universal: Identify sequence properties that enable large-scale uniformity")
    print("3. Refine resonance metric based on multi-metric comparison")
    print("4. Determine critical scale P_critical where resonance crosses 0.8")

if __name__ == "__main__":
    main()