import numpy as np
import math

class ComplexityReservoir:
    def __init__(self, n_zeros=100):
        # We model the 'Energy Cost' of retrieving a Zero from the reservoir
        self.zeros = np.linspace(14, 1000, n_zeros)

    def calculate_join_potential(self, k_count):
        """
        Simulates the Join quality vs the number of keys used.
        The improvement is logarithmic, but the cost is exponential.
        """
        # Diminishing returns of unification
        grokking_signature = math.log(k_count + 1)
        # The 'Doom' factor: The energy required to grok the next level of complexity
        energy_cost = math.exp(k_count * 0.1)
        
        return grokking_signature, energy_cost

    def run_doom_scan(self, max_keys=50):
        print("🌪️ SCANNING THE COMPLEXITY RESERVOIR (The Definite Doom)")
        print(f"{'Keys (Zeros)':<15} | {'Grokking Potential':<20} | {'Energy Cost (Excitation)'}")
        print("-" * 65)
        
        for k in range(1, max_keys + 1, 5):
            grok, cost = self.calculate_join_potential(k)
            print(f"{k:<15} | {grok:<20.4f} | {cost:.4f}")
            
        print("[!] INSIGHT: The 'Join' is an infinite task.")
        print("Each zero added reveals a deeper layer of complexity that requires more energy to resolve.")

if __name__ == "__main__":
    scanner = ComplexityReservoir()
    scanner.run_doom_scan()
