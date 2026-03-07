import math

class GPUEngine:
    def __init__(self, phi_L=0.5, epsilon=0.1):
        """
        phi_L: Phase-Locking Coefficient (0.5 = Our Arithmetic Universe)
        epsilon: ABC Conjecture elasticity
        """
        self.phi_L = phi_L
        self.epsilon = epsilon
        self.primes = [2, 3]
        self.total_entropy = 0.0
        self.history = []

    def get_radical(self, n):
        """Calculates the product of distinct prime factors (Thermal Density)."""
        if n < 1: return 1
        factors = set()
        d, temp_n = 2, n
        while d * d <= temp_n:
            if temp_n % d == 0:
                factors.add(d)
                while temp_n % d == 0:
                    temp_n //= d
            d += 1
        if temp_n > 1: factors.add(temp_n)
        
        res = 1
        for f in factors: res *= f
        return res

    def process_n(self, n):
        """The N+1 Detector Operator: Determines the Phase-State of n."""
        state = "UNDEFINED"
        detail = ""

        # 1. Binary Condensation (Even Lock)
        if n % 2 == 0:
            for p in self.primes:
                if (n - p) in self.primes:
                    state = "EVEN_CONDENSATE"
                    detail = f"Locked: {p} + {n-p}"
                    break
        
        # 2. Ternary Equilibrium (Odd Gas)
        if state == "UNDEFINED" and n % 2 != 0:
            found = False
            for i in range(len(self.primes)):
                for j in range(i, len(self.primes)):
                    comp = n - (self.primes[i] + self.primes[j])
                    if comp in self.primes:
                        state = "ODD_EQUILIBRIUM"
                        detail = f"Equilibrium: {self.primes[i]}+{self.primes[j]}+{comp}"
                        found = True
                        break
                if found: break

        # 3. Axiomatic Emergence (New Prime Birth)
        # If no resonance is found, a new singularity is forced.
        if state == "UNDEFINED":
            self.primes.append(n)
            self.total_entropy += math.log(n)
            state = "AXIOMATIC_EMERGENCE"
            detail = "NEW PRIME BORN"
            
            # ABC Surface Tension Check
            # Comparing C to Radical(ABC) where A+B=C. 
            # Simplified for N+1 growth: C=n, A=n-1, B=1
            rad_abc = self.get_radical(n * (n - 1))
            if n > (rad_abc ** (1 + self.epsilon)):
                state = "ROGUE_AXIOM"
                detail = "ABC TENSION BREACH"

        self.history.append((n, state, detail))
        return state, detail

    def run_simulation(self, limit):
        print(f"{'N':<5} | {'STATE':<20} | {'LOGIC DETAIL'}")
        print("-" * 55)
        for i in range(4, limit + 1):
            state, detail = self.process_n(i)
            if "AXIOMATIC" in state or "ROGUE" in state:
                # Highlight the growth moments
                print(f"\033[91m{i:<5} | {state:<20} | {detail}\033[0m")
            else:
                print(f"{i:<5} | {state:<20} | {detail}")
        
        print("-" * 55)
        print(f"Final Axiomatic Entropy: {self.total_entropy:.4f}")
        print(f"Total Unique Axioms Generated: {len(self.primes)}")

# --- EXECUTION ---
engine = GPUEngine(phi_L=0.5)
engine.run_simulation(limit=100)