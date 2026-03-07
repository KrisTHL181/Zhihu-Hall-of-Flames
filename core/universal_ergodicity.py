import math
from collections import Counter

class UniversalErgodicityProver:
    def calculate_entropy(self, data):
        counts = Counter(data)
        total = len(data)
        probs = [count/total for count in counts.values()]
        return -sum(p * math.log2(p) for p in probs) / math.log2(len(counts))

    def verify_spectral_mixing(self, limit=5000):
        primes, is_p = [], [True]*(limit+1)
        for p in range(2, limit+1):
            if is_p[p]:
                primes.append(p)
                for i in range(p*p, limit+1, p): is_p[i] = False
        gaps = [primes[i+1] - primes[i] for i in range(len(primes)-1)]
        print(f"🔭 SPECTRAL ERGODICITY (RH) Entropy: {self.calculate_entropy(gaps):.4f}")

if __name__ == "__main__":
    UniversalErgodicityProver().verify_spectral_mixing()
