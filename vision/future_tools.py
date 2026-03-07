import math

class CollatzHamiltonian:
    def __init__(self):
        self.decadic_anchors = {8, 18, 28, 38, 48, 58, 68, 78, 88, 98}

    def energy(self, n):
        """
        Calculates the Total Energy of a number state 'n'.
        E = Kinetic (Magnitude) - Potential (Decadic Grip)
        """
        if n == 1: return 0
        
        # Kinetic Energy: Log-Magnitude (Tendency to fly off)
        # Using log2 because Collatz is a binary process.
        kinetic = math.log2(n)
        
        # Potential Energy: The 'Grip' of the Base-10 structure.
        # If n is close to a Decadic Anchor, potential is high (strong grip).
        # We model this as a 'Gravity Well' around x mod 10 = 8.
        residue = n % 10
        dist_to_8 = min(abs(residue - 8), abs(residue + 2)) # Cyclical distance
        
        # Potential scales with log(n) because the lattice is 'stiff'.
        # Constants tuned to match empirical observation.
        potential = (1.0 / (dist_to_8 + 1)) * 0.5 * math.log2(n)
        
        return kinetic - potential

    def run_orbit(self, start_n):
        print(f"🌀 COLLATZ HAMILTONIAN TRACKER (n={start_n})")
        print(f"{'Step':<5} | {'Value':<15} | {'Energy (E)':<12} | {'dE/dt'}")
        print("-" * 55)
        
        curr = start_n
        prev_E = self.energy(curr)
        steps = 0
        
        while curr != 1:
            if curr % 2 == 0:
                curr //= 2
            else:
                curr = 3 * curr + 1
            
            curr_E = self.energy(curr)
            dE = curr_E - prev_E
            
            # Highlight Energy Drops
            color = "\033[92m" if dE < 0 else "\033[91m"
            print(f"{steps+1:<5} | {curr:<15} | {curr_E:<12.4f} | {color}{dE:+.4f}\033[0m")
            
            prev_E = curr_E
            steps += 1
            if steps > 100: break

class ResonanceEchoScanner:
    def __init__(self, beta=1.0):
        self.beta = beta
        self.axioms = [2, 3]

    def is_axiom(self, n):
        # Simplified LSE check for Phase-Locking
        # Returns True if 'n' cannot be formed by existing axioms
        # (Simulating Prime Birth)
        limit = math.isqrt(n) + 1
        for p in self.axioms:
            if p > limit: break
            if n % p == 0:
                return False
        return True

    def scan(self, limit=1000):
        print(f"📡 RESONANCE ECHO SCANNER (Twin Prime Detection)")
        print(f"Scanning for Logic Shocks in range [1, {limit}]...")
        
        prime_births = []
        double_shocks = 0
        
        for i in range(4, limit + 1):
            if self.is_axiom(i):
                self.axioms.append(i)
                prime_births.append(i)
                
                # Check for "Echo" (Twin Prime)
                if (i - 2) in prime_births:
                    double_shocks += 1
                    # Visualizing the Shockwave
                    print(f"⚡ SHOCKWAVE DETECTED: {i-2} <--> {i} (Gap: 2)")
        
        probability = double_shocks / len(prime_births)
        print("-" * 50)
        print(f"Total Primes: {len(prime_births)}")
        print(f"Twin Shocks:  {double_shocks}")
        print(f"Echo Probability: {probability:.4f}")
        print(f"Status: {'CRITICAL RESONANCE' if probability > 0 else 'DAMPED'}")

if __name__ == "__main__":
    # Tool 1: Hamiltonian
    ham = CollatzHamiltonian()
    ham.run_orbit(27) # The famous long-runner
    
    # Tool 2: Resonance Echo
    echo = ResonanceEchoScanner()
    echo.scan(limit=200)
