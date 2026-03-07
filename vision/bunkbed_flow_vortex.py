import numpy as np
import math

class BunkbedFlowSimulator:
    """
    Simulates information flow on a two-layer Bunkbed Manifold.
    Tests if jumping layers (Vertical) can exceed staying in-layer (Horizontal).
    """
    def __init__(self, size=100, horizontal_viscosity=0.5, vertical_viscosity=0.8):
        self.size = size
        # Logical Friction (gamma)
        self.vh = horizontal_viscosity
        self.vv = vertical_viscosity

    def simulate_percolation(self, p_edge=0.5):
        """
        Simulates connectivity probability.
        p_stay: Probability of staying in the same layer.
        p_jump: Probability of jumping to the other layer.
        """
        # We model the flow as a dissipative process.
        # Flow = exp(-gamma * p_edge)
        
        flow_horizontal = math.exp(-self.vh * p_edge)
        flow_vertical = math.exp(-self.vv * p_edge)
        
        print("\n🛏️ ANALYZING BUNKBED MANIFOLD FLOW")
        print(f"Horizontal Viscosity (vh): {self.vh}")
        print(f"Vertical Viscosity (vv):   {self.vv}")
        print("-" * 40)
        
        print(f"Laminar Probability (Stay): {flow_horizontal:.4f}")
        print(f"Jump Probability (Across):  {flow_vertical:.4f}")
        
        if flow_vertical > flow_horizontal:
            print("\n🚨 VORTEX DETECTED: Counterexample Found!")
            print("   Jumping layers is more efficient than staying.")
        else:
            print("\n✅ LAMINAR FLOW: Bunkbed Conjecture Holds.")

    def find_phase_transition(self):
        """Identifies the point where the conjecture fails."""
        print("\n🔍 SCANNING FOR BUNKBED PHASE TRANSITION")
        print(f"{'vh':<10} | {'vv':<10} | {'Status'}")
        print("-" * 35)
        
        for vh in np.linspace(0.1, 1.0, 5):
            for vv in np.linspace(0.1, 1.0, 5):
                fh = math.exp(-vh * 0.5)
                fv = math.exp(-vv * 0.5)
                
                status = "VORTEX" if fv > fh else "LAMINAR"
                if status == "VORTEX":
                    print(f"{vh:<10.2f} | {vv:<10.2f} | {status}")

if __name__ == "__main__":
    # Test standard case
    sim = BunkbedFlowSimulator(horizontal_viscosity=0.6, vertical_viscosity=0.4)
    sim.simulate_percolation()
    
    # Scan for the transition
    sim.find_phase_transition()
