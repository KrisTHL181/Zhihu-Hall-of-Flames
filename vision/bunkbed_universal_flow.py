import numpy as np
import math
from core.spectral_gap_analyzer import SpectralGapAnalyzer
from core.information_decay_meter import InformationDecayMeter

class UniversalBunkbedAnalyzer:
    """
    Analyzes the Bunkbed Problem using Universal Core Bricks.
    Uses Spectral Gap (Delta) and Information Decay (dS/dt).
    """
    def __init__(self, size=100):
        self.analyzer = SpectralGapAnalyzer(n_states=10)
        self.meter = InformationDecayMeter()

    def calculate_spectral_flow(self, sequence, viscosity):
        """Calculates flow as a function of the Spectral Gap and Viscosity."""
        gap = self.analyzer.calculate_spectral_gap(sequence)
        # Flow = exp(-(1/Gap) * Viscosity) - following the Percolation Brick
        if gap <= 0: return 0
        return math.exp(-(1.0 / gap) * viscosity)

    def analyze_manifold_connectivity(self, h_visc=0.5, v_visc=0.2):
        print("🧱 ANALYZING BUNKBED MANIFOLD (ADS-SGT Universal Approach)")
        print(f"Horizontal Viscosity: {h_visc}")
        print(f"Vertical Coupling:   {v_visc}")
        print("-" * 55)
        
        # 1. Generate an 'Adelic' sequence for the graph layers
        # Using a stochastic sequence to represent a complex graph structure
        np.random.seed(42)
        seq = np.random.randint(0, 10, 1000)
        
        # 2. Measure the Universal Spectral Gap
        gap = self.analyzer.calculate_spectral_gap(seq)
        print(f"Universal Spectral Gap (Delta): {gap:.4f}")
        
        # 3. Calculate Flow using the Percolation Law Brick
        flow_h = self.calculate_spectral_flow(seq, h_visc)
        flow_v = self.calculate_spectral_flow(seq, v_visc)
        
        print(f"Horizontal Flow (In-layer): {flow_h:.4f}")
        print(f"Vertical Flow (Cross-layer): {flow_v:.4f}")
        
        # 4. Thermodynamic Verification
        s_h = self.meter.calculate_logical_entropy(int(flow_h * 1000))
        s_v = self.meter.calculate_logical_entropy(int(flow_v * 1000))
        
        print(f"In-layer Entropy (S_h):     {s_h:.4f}")
        print(f"Cross-layer Entropy (S_v):  {s_v:.4f}")
        
        if flow_v > flow_h:
            print("🚨 VORTEX DETECTED: Symmetry Broken via Spectral Coupling.")
            print("   The Adelic Fiber Bundle has entered a Superfluid state.")
        else:
            print("✅ LAMINAR FLOW: Ground State Stability Maintained.")

if __name__ == "__main__":
    # Test a case where vertical coupling is stronger than horizontal friction
    # (The counterexample scenario)
    explorer = UniversalBunkbedAnalyzer()
    explorer.analyze_manifold_connectivity(h_visc=0.8, v_visc=0.1)
