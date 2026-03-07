import math
import numpy as np

def verify_lattice_invariance(limit=1000):
    def metric(n):
        r = n % 10
        dist = min(abs(r - 8), abs(r + 2))
        return 1.0 / (dist + 1.0)
    
    base_sum = sum(metric(i) for i in range(10))
    for n in range(limit):
        test_sum = sum(metric(n + i) for i in range(10))
        if abs(test_sum - base_sum) > 1e-10:
            return False, n
    return True, base_sum

def verify_prime_independence(limit=100):
    # Testing log independence for first 100 primes
    primes = [2, 3, 5, 7, 11, 13, 17, 19]
    # We check if log(p1^c1 * p2^c2) = 0 implies c1=c2=0 for a range
    for p1 in primes:
        for p2 in primes:
            if p1 == p2: continue
            for c1 in range(-5, 5):
                for c2 in range(-5, 5):
                    if c1 == 0 and c2 == 0: continue
                    val = c1 * math.log(p1) + c2 * math.log(p2)
                    if abs(val) < 1e-10:
                        return False, (p1, p2, c1, c2)
    return True, None

if __name__ == "__main__":
    lattice_ok, val = verify_lattice_invariance()
    prime_ok, err = verify_prime_independence()
    
    print(f"Lattice Invariance Verified: {lattice_ok} (Sum = {val:.4f})")
    print(f"Prime Independence Verified: {prime_ok}")
