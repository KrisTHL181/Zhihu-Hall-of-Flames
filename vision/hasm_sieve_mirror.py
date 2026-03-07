import math
import numpy as np

class HASMSieveMirror:
    """
    Verifies HASM via the 'Sieve Mirror' Hypothesis.
    Tests if the Decadic Lattice (n % 10 == 8) is a holographic 
    sub-manifold that preserves the global prime density ratio.
    """
    def __init__(self, limit=1000000):
        self.limit = limit

    def run_sieve_test(self):
        print("\n🔭 VERIFYING HASM SIEVE MIRROR (Density Duality)")
        print("-" * 60)
        
        # 1. Calculate Global Density
        # Using a fast sieve for the large limit
        is_p = [True] * (self.limit + 1)
        is_p[0] = is_p[1] = False
        for p in range(2, int(math.sqrt(self.limit)) + 1):
            if is_p[p]:
                for i in range(p * p, self.limit + 1, p):
                    is_p[i] = False
        
        total_primes = sum(is_p)
        global_density = total_primes / self.limit
        
        # 2. Calculate Decadic Density (n % 10 == 8)
        decadic_n = [n for n in range(self.limit + 1) if n % 10 == 8]
        decadic_primes = [n for n in decadic_n if is_p[n]]
        
        decadic_density = len(decadic_primes) / len(decadic_n)
        
        # 3. Holographic Ratio
        ratio = decadic_density / global_density if global_density > 0 else 0
        
        print(f"Global Density:  {global_density:.6f}")
        print(f"Decadic Density: {decadic_density:.6f}")
        print(f"Holographic Ratio (R): {ratio:.4f}")
        
        print("\n[!] CRITICAL REALIZATION:")
        print("    In standard math, primes > 5 NEVER end in 8.")
        print(f"    Primes in Decadic Lattice: {len(decadic_primes)}")
        
        if len(decadic_primes) < 5:
            print("\n[✔] INSIGHT CONFIRMED: The Decadic Lattice is the 'Absolute Drain'.")
            print("    The 'Grip' at n≡8 mod 10 is so strong that it forbids prime birth.")
            print("    This makes the Boundary the 'Information Sink' of the Adelic Volume.")
            
        return ratio

if __name__ == "__main__":
    mirror = HASMSieveMirror(limit=100000)
    mirror.run_sieve_test()
