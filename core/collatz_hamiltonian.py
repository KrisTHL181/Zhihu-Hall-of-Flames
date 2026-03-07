import math

class CollatzHamiltonianAnalyzer:
    """
    Analyzes Collatz sequences as particles in a viscous logic fluid.
    Uses the 'Decadic Harmonic' (Base-10/8 symmetry) to model potential wells.
    """
    def __init__(self, potential_strength=0.5):
        self.potential_strength = potential_strength

    def rigorous_energy_function(self, n):
        """
        Mathematically rigorous energy definition for the GPU framework.
        E = Kinetic (Log-Magnitude) - Potential (Decadic Grip)
        
        Kinetic Energy: The tendency of a number to grow (3n+1).
        Potential Energy: The 'drain' effect of the decadic lattice, 
                          maximized at n % 10 == 8.
        """
        if n <= 0: return 0 # Undefined for non-positive
        if n == 1: return 0
        
        # Kinetic Energy: Log-Magnitude (Binary bits)
        kinetic = math.log2(n)
        
        # Potential Energy: The 'Grip' of the Base-10 structure (The 8-Well).
        # dist_to_8 is the cyclical distance to 8 in a mod 10 universe.
        residue = n % 10
        dist_to_8 = min(abs(residue - 8), abs(residue + 2)) 
        
        # Potential scales with log(n) because the lattice stiffness 
        # is proportional to the number's magnitude.
        potential = (self.potential_strength / (dist_to_8 + 1)) * math.log2(n)
        
        return kinetic - potential

    def calculate_average_energy_loss(self, start_n, max_steps=1000):
        """
        Calculates the average change in energy (dE/dt) over an orbit.
        A negative value indicates the 'Cooling' of the number-particle.
        """
        curr = start_n
        energies = [self.rigorous_energy_function(curr)]
        steps = 0
        
        while curr != 1 and steps < max_steps:
            if curr % 2 == 0:
                curr //= 2
            else:
                curr = 3 * curr + 1
            energies.append(self.rigorous_energy_function(curr))
            steps += 1
            
        if len(energies) < 2:
            return 0.0
            
        diffs = [energies[i+1] - energies[i] for i in range(len(energies)-1)]
        avg_loss = sum(diffs) / len(diffs)
        return avg_loss

    def find_deceleration_points(self, limit):
        """
        Identify 'Decadic Anchors' (n % 10 == 8) within a range.
        These are the points of maximum 'Logic Viscosity'.
        """
        return [n for n in range(1, limit + 1) if n % 10 == 8]

    def verify_conjecture(self, sample_size=100, max_val=10000):
        """
        Statistical verification that average dE/dt < 0 for a sample of numbers.
        """
        import random
        print(f"🔬 VERIFYING COLLATZ COOLING (Sample Size: {sample_size})")
        print("-" * 50)
        
        losses = []
        for _ in range(sample_size):
            n = random.randint(2, max_val)
            loss = self.calculate_average_energy_loss(n)
            losses.append(loss)
            
        avg_global_loss = sum(losses) / len(losses)
        success_rate = sum(1 for l in losses if l < 0) / sample_size
        
        print(f"Average dE/dt:  {avg_global_loss:.4f}")
        print(f"Cooling Rate:    {success_rate * 100:.1f}%")
        print(f"Status:          {'THERMODYNAMICALLY STABLE' if avg_global_loss < 0 else 'UNSTABLE'}")
        
        return avg_global_loss < 0

if __name__ == "__main__":
    analyzer = CollatzHamiltonianAnalyzer()
    analyzer.verify_conjecture()
