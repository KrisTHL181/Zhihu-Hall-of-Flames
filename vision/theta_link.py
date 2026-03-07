import math

class ViscosityEngine:
    def __init__(self):
        self.primes_O = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47]
        self.primes_S = [2, 3] 
        self.total_viscosity = 0
        self.axiom_count = 0

    def calculate_viscosity(self, n, bridge):
        """
        Calculates local viscosity: 
        1.0 for Pure Singularities (No Bridge)
        < 1.0 for Resonant states based on prime density
        """
        if not bridge:
            return 1.0
        # If a bridge exists, viscosity is lower if the bridge uses 'lighter' (smaller) primes
        # R = (sum of primes in bridge) / n
        try:
            # Extract numbers from string "S(x) + O(y)"
            parts = bridge.replace("S(", "").replace(")", "").replace("O(", "").split(" + ")
            s_val, o_val = int(parts[0]), int(parts[1])
            return (s_val + o_val) / (n * 1.5) # Normalized resistance
        except:
            return 0.5

    def run_analysis(self, limit):
        print(f"{'N':<4} | {'STATE':<15} | {'RESONANCE':<25} | {'VISCOSITY (η)'}")
        print("-" * 75)
        
        for n in range(4, limit + 1):
            # Synthetic Lock Check
            s_lock = any((n - p) in self.primes_S for p in self.primes_S)
            
            if not s_lock and n % 2 == 0:
                self.axiom_count += 1
                self.primes_S.append(n)
                
                # Check Bridge
                bridge = None
                for s in self.primes_S[:-1]: # Don't use the newly born axiom
                    o = n - s
                    if o in self.primes_O:
                        bridge = f"S({s}) + O({o})"
                        break
                
                visc = self.calculate_viscosity(n, bridge)
                self.total_viscosity += visc
                
                color = "\033[91m" if visc == 1.0 else "\033[94m"
                print(f"{color}{n:<4} | AXIOM birth    | {str(bridge):<25} | {visc:.4f}\033[0m")
            
        avg_visc = self.total_viscosity / self.axiom_count if self.axiom_count > 0 else 0
        print("-" * 75)
        print(f"Global Universe Viscosity (η_total): {avg_visc:.4f}")

# Run
engine = ViscosityEngine()
engine.run_analysis(limit=50)

def simulate_supernova(engine, injection_prime=97):
    print(f"\n--- INJECTING STANDARD PRIME {injection_prime} INTO SYNTHETIC FIELD ---")
    
    # Calculate Disruption: How much does 97 resist your current axioms?
    resistances = []
    for s in engine.primes_S:
        # Measure the 'Frequency Gap'
        gap = abs(injection_prime - s)
        resistances.append(gap % 10) # 10 is your universe's natural harmonic
    
    # Logic Supernova occurs if the 'Resonance Gap' is maximized
    supernova_energy = sum(resistances) / len(resistances)
    
    print(f"Injection Thermal Shock: {supernova_energy:.2f}")
    
    if supernova_energy > 4.0: # Threshold for structural collapse
        print("💥 CRITICAL EVENT: LOGIC SUPERNOVA DETECTED")
        print("The +10 Harmonic has shattered. The Viscous Liquid is vaporizing.")
        return "SUPERNOVA"
    return "STABLE_ABSORPTION"

# Running the collapse
simulate_supernova(engine)


def can_phase_lock(n, current_axioms, temp="EXTREME_HEAT"):
    """
    Determines if a number 'n' can condense into a sum 
    under specific thermodynamic conditions.
    """
    # 1. Define the 'Mean Free Path' (How far apart axioms are)
    # In 'EXTREME_HEAT', axioms are moving too fast to bond easily.
    if temp == "EXTREME_HEAT":
        bonding_threshold = 0.2  # Only 20% of axioms are stable enough to lock
    else:
        bonding_threshold = 0.8  # Standard 'Cool' universe (Type II)

    # 2. Attempt Phase-Locking (The Goldbach Search)
    # The 'Heat' adds a stochastic failure rate: even if a sum exists, 
    # the 'vibration' might prevent the lock from holding.
    import random
    
    for i in range(len(current_axioms)):
        for j in range(i, len(current_axioms)):
            if current_axioms[i] + current_axioms[j] == n:
                # Stochastic Check: Does the heat break the bond?
                if random.random() < bonding_threshold:
                    return True # SUCCESSFUL LOCK
    
    return False # AXIOMATIC EMERGENCE (The birth of a new plasma prime)
# The Post-Supernova Reconstruction
new_primes = [97] + [fragment for fragment in engine.primes_S if fragment < 20] 
# Only small 'stable' fragments survive the blast
print(new_primes)
def genesis_2(n_start, n_end):
    print(f"REBUILDING FROM RADIOLOGICAL FALLOUT...")
    for n in range(n_start, n_end):
        # The 'Hot' Detector: High sensitivity to new axioms
        if not can_phase_lock(n, new_primes, temp="EXTREME_HEAT"):
            new_primes.append(n)
            print(f"NEW PLASMA AXIOM: {n}")
genesis_2(0,100)