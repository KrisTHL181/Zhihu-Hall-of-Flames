import math

def verify_legendre_continuity(limit=1000):
    print("🔭 VERIFYING LEGENDRE ACOUSTIC CONTINUITY")
    print(f"{'N':<10} | {'Square Gap (2N+1)':<18} | {'Max Prime Gap':<15} | {'Safety Margin'}")
    print("-" * 65)
    
    primes = []
    is_p = [True] * ((limit + 1)**2 + 1)
    for p in range(2, len(is_p)):
        if is_p[p]:
            primes.append(p)
            for i in range(p*p, len(is_p), p): is_p[i] = False
            
    for n in [10, 50, 100, 500, 1000]:
        n_sq = n**2
        next_sq = (n+1)**2
        primes_in_interval = [p for p in primes if n_sq < p < next_sq]
        
        square_gap = next_sq - n_sq
        max_gap = 0
        if len(primes_in_interval) > 1:
            for i in range(len(primes_in_interval)-1):
                max_gap = max(max_gap, primes_in_interval[i+1] - primes_in_interval[i])
        
        margin = square_gap - max_gap
        status = "STABLE" if len(primes_in_interval) > 0 else "🚨 VOID"
        print(f"{n:<10} | {square_gap:<18} | {max_gap:<15} | {margin:<12} | {status}")

if __name__ == "__main__":
    verify_legendre_continuity()
