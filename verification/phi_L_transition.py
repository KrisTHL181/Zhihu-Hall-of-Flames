import math
import matplotlib.pyplot as plt

class TransitionEngine:
    def __init__(self, phi_L):
        self.phi_L = phi_L
        self.primes = [2, 3]
        self.axioms = 0

    def process_n(self, n):
        # 1. Binary Lock Check (Even)
        if n % 2 == 0:
            for p in self.primes:
                if (n - p) in self.primes:
                    # Random Check: Does the Ph_L allow the lock to hold?
                    import random
                    if random.random() < self.phi_L:
                        return "LOCK"
        
        # 2. Ternary Lock Check (Odd)
        else:
            found = False
            for i in range(len(self.primes)):
                for j in range(i, len(self.primes)):
                    comp = n - (self.primes[i] + self.primes[j])
                    if comp in self.primes:
                        import random
                        if random.random() < self.phi_L:
                            return "LOCK"
        
        # 3. Axiomatic Emergence
        self.primes.append(n)
        self.axioms += 1
        return "AXIOM"

def run_experiment(limit=200):
    phi_values = [0.0, 0.2, 0.4, 0.6, 0.8, 1.0]
    results = []
    
    print(f"{'phi_L':<10} | {'AXIOM DENSITY (%)':<15} | {'UNIVERSE TYPE'}")
    print("-" * 45)
    
    for phi in phi_values:
        engine = TransitionEngine(phi)
        for i in range(4, limit + 1):
            engine.process_n(i)
        
        density = (engine.axioms / limit) * 100
        
        if phi == 0.0: utype = "SUPERFLUID"
        elif phi < 0.4: utype = "HOT GAS"
        elif phi < 0.7: utype = "ARITHMETIC (Ours)"
        elif phi < 0.9: utype = "COOLING SOLID"
        else: utype = "CRYSTALLINE"
        
        results.append(density)
        print(f"{phi:<10.1f} | {density:<15.1f} | {utype}")

    # Plotting for visual confirmation
    plt.figure(figsize=(10, 6))
    plt.plot(phi_values, results, 'r-o', linewidth=2)
    plt.title("Axiomatic Transition: The Phase-Locking Gradient")
    plt.xlabel("Phase-Locking Coefficient (phi_L)")
    plt.ylabel("Axiomatic Density (%)")
    plt.grid(True)
    plt.savefig("verification/transition_graph.png")
    print("\n[✔] Experiment Complete. Transition graph saved to 'verification/transition_graph.png'.")

if __name__ == "__main__":
    run_experiment()
