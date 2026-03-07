import math
import numpy as np

class DecadicLatticeAnalyzer:
    """
    Formalizes the study of Base-10 gravitational effects on the 
    Gaseous Prime Universe. Focuses on the 10-Lattice and 8-Singularity.
    """
    def __init__(self, lattice_constant=10, singularity=8):
        self.lattice_constant = lattice_constant
        self.singularity = singularity

    def calculate_gravity_well(self, n):
        """
        Calculates the 'Gravitational Potential' (Phi_G) at a number 'n'.
        Phi_G is maximized when n is close to the Singularity (8 mod 10).
        """
        residue = n % self.lattice_constant
        # Cyclical distance in the lattice
        dist = min(abs(residue - self.singularity), 
                   abs(residue + (self.lattice_constant - self.singularity)))
        
        # Potential is inversely proportional to distance (Newtonian style)
        # We add 1 to avoid division by zero.
        potential = 1.0 / (dist + 1)
        return potential

    def study_8_singularity(self, limit=1000):
        """
        Analyzes how numbers ending in 8 act as 'Logic Drains'.
        Tracks the 2-adic depth (Halving capacity) of these numbers.
        """
        print(f"🕳️ ANALYZING THE {self.singularity}-SINGULARITY (Limit: {limit})")
        print(f"{'n':<10} | {'Potential':<12} | {'2-adic Depth'}")
        print("-" * 40)
        
        anchors = [n for n in range(1, limit + 1) if n % self.lattice_constant == self.singularity]
        depths = []
        
        for a in anchors[:10]: # Just show first 10
            # How many times can we divide by 2?
            temp = a
            depth = 0
            while temp > 0 and temp % 2 == 0:
                depth += 1
                temp //= 2
            depths.append(depth)
            pot = self.calculate_gravity_well(a)
            print(f"{a:<10} | {pot:<12.4f} | {depth}")
            
        avg_depth = sum(depths) / len(depths) if depths else 0
        print(f"Average 2-adic Depth: {avg_depth:.2f}")
        return avg_depth >= 3.0 # The 'Triple Halving' property

    def connect_to_p_adic(self, n, p=5):
        """
        Connects the 10-lattice to p-adic analysis.
        Since 10 = 2 * 5, the 5-adic component is the 'Phase-Lock'.
        """
        # Calculate 5-adic valuation
        v_5 = 0
        temp = n
        if temp == 0: return float('inf')
        while temp % p == 0:
            v_5 += 1
            temp //= p
            
        print(f"🔗 p-adic Link (p={p}): n={n} -> v_{p}={v_5}")
        return v_5

if __name__ == "__main__":
    lattice = DecadicLatticeAnalyzer()
    lattice.study_8_singularity()
    lattice.connect_to_p_adic(810, p=5)
    lattice.connect_to_p_adic(8, p=2)
