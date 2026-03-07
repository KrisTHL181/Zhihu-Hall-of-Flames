import math

class ColdUniverseEngine:
    def __init__(self, phi_L=1.0):
        """
        phi_L: Phase-Locking Coefficient (1.0 = Crystalline/Absolute Zero)
        In this universe, the 'Bonding Strength' is so high that even
        distant resonances are captured.
        """
        self.phi_L = phi_L
        self.axioms = [1] # 1 is the original seed
        self.history = []

    def process_n(self, n):
        # In a Cold Universe, ANY combination of previous axioms 
        # that sums to 'n' results in a lock.
        # We allow recursive partitioning (any number of terms).
        
        # Check if 'n' can be formed by any sum of existing axioms
        # In phi_L = 1.0, the 'Greedy Siphon' is active.
        temp_n = n
        components = []
        for a in reversed(self.axioms):
            while temp_n >= a:
                temp_n -= a
                components.append(a)
        
        if temp_n == 0:
            state = "CRYSTALLINE_LOCK"
            detail = f"Fused from: {' + '.join(map(str, components))}"
        else:
            # This should theoretically never happen if 1 is an axiom
            self.axioms.append(n)
            state = "AXIOM_BIRTH"
            detail = "NEW SINGULARITY"
            
        self.history.append((n, state, detail))
        return state, detail

    def run(self, limit=50):
        print(f"❄️ SIMULATING COLD UNIVERSE (phi_L = {self.phi_L})")
        print(f"{'N':<5} | {'STATE':<20} | {'RESONANCE DETAIL'}")
        print("-" * 60)
        for i in range(2, limit + 1):
            state, detail = self.process_n(i)
            print(f"{i:<5} | {state:<20} | {detail}")
        
        print("-" * 60)
        print(f"Final Axiom Count: {len(self.axioms)}")
        print("RESULT: 100% PHASE-LOCK ACHIEVED. UNIVERSE IS A STATIC CRYSTAL.")

if __name__ == "__main__":
    engine = ColdUniverseEngine()
    engine.run()
