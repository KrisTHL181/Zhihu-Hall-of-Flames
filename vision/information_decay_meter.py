import math
import numpy as np

class InformationDecayMeter:
    def __init__(self, window_size=20):
        self.window_size = window_size

    def calculate_logical_entropy(self, value):
        """
        Calculates the Shannon Entropy of a number's bit-distribution.
        Primes should have high entropy (Incompressible).
        Composites should have lower entropy (Phase-Locked).
        """
        if value <= 1: return 0
        binary = bin(value)[2:]
        counts = {'0': binary.count('0'), '1': binary.count('1')}
        total = len(binary)
        entropy = -sum((count/total) * math.log2(count/total) for count in counts.values() if count > 0)
        return entropy

    def measure_decay(self, name, sequence):
        print(f"🌡️ MEASURING INFORMATION DECAY: {name}")
        print(f"{'Step':<5} | {'Value':<12} | {'Entropy (S)':<12} | {'Decay Rate (γ)'}")
        print("-" * 55)
        
        entropies = [self.calculate_logical_entropy(v) for v in sequence]
        
        for i in range(len(sequence)):
            if i % (len(sequence)//10 or 1) == 0 or i == len(sequence)-1:
                gamma = (entropies[i-1] - entropies[i]) if i > 0 else 0
                color = "\033[92m" if gamma > 0 else "\033[91m"
                print(f"{i:<5} | {sequence[i]:<12} | {entropies[i]:<12.4f} | {color}{gamma:+.4f}\033[0m")
        
        total_decay = entropies[0] - entropies[-1]
        print(f"Total Logic Information Dissipated: {total_decay:.4f}")
        print(f"Status: {'DECAYING (Stable)' if total_decay > 0 else 'EXCITED (Axiomatic)'}\n")

if __name__ == "__main__":
    meter = InformationDecayMeter()
    
    # 1. Collatz Decay: From a high-entropy seed (27) to a low-entropy cycle
    n, seq = 27, [27]
    while n != 1:
        n = n // 2 if n % 2 == 0 else 3 * n + 1
        seq.append(n)
        if len(seq) > 200: break
    meter.measure_decay("Collatz Orbit (n=27)", seq)

    # 2. Prime Emergence: Primes shouldn't decay; they should stay 'Hot'
    def get_primes(n):
        primes, is_p = [], [True]*(n+1)
        for p in range(2, n+1):
            if is_p[p]:
                primes.append(p)
                for i in range(p*p, n+1, p): is_p[i] = False
        return primes
    primes = get_primes(500)
    meter.measure_decay("Prime Birth Sequence (Emergence)", primes)
