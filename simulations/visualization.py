import matplotlib.pyplot as plt
import numpy as np
import math
from core.hardmath_attack.collatz_hamiltonian import CollatzHamiltonianAnalyzer
from core.hardmath_attack.resonance_statistics import ResonanceStatistics

class GPUVisualizer:
    """
    Visualization suite for the Gaseous Prime Universe framework.
    Provides graphical insights into Collatz energy and Prime distributions.
    """
    def __init__(self):
        self.ham_analyzer = CollatzHamiltonianAnalyzer()
        self.res_stats = ResonanceStatistics()

    def plot_collatz_orbit(self, start_n, save_path="collatz_energy_plot.png"):
        """Plots the Hamiltonian Energy of a Collatz orbit."""
        curr = start_n
        steps = [0]
        energies = [self.ham_analyzer.rigorous_energy_function(curr)]
        values = [curr]
        
        while curr != 1 and len(steps) < 500:
            if curr % 2 == 0:
                curr //= 2
            else:
                curr = 3 * curr + 1
            steps.append(steps[-1] + 1)
            energies.append(self.ham_analyzer.rigorous_energy_function(curr))
            values.append(curr)
            
        fig, ax1 = plt.subplots(figsize=(10, 6))
        
        ax1.set_xlabel('Step')
        ax1.set_ylabel('Energy (E)', color='tab:blue')
        ax1.plot(steps, energies, color='tab:blue', label='Hamiltonian Energy')
        ax1.tick_params(axis='y', labelcolor='tab:blue')
        
        ax2 = ax1.twinx()
        ax2.set_ylabel('Value (n)', color='tab:red')
        ax2.plot(steps, values, color='tab:red', alpha=0.3, label='Value (n)')
        ax2.tick_params(axis='y', labelcolor='tab:red')
        
        plt.title(f"Collatz Hamiltonian Orbit for n={start_n}")
        fig.tight_layout()
        plt.savefig(save_path)
        print(f"📊 Collatz energy plot saved to {save_path}")
        plt.close()

    def plot_p_echo_stability(self, max_N=10000, save_path="p_echo_stability.png"):
        """Plots the P_echo (Resonance strength) stability across scales."""
        scales = np.logspace(2, math.log10(max_N), 20, dtype=int)
        p_echos = []
        
        for s in scales:
            _, _, p = self.res_stats.calculate_p_echo(s)
            p_echos.append(p)
            
        plt.figure(figsize=(10, 6))
        plt.semilogx(scales, p_echos, 'o-', label='P_echo (Shock Strength)')
        plt.xlabel('Scale (N)')
        plt.ylabel('P_echo')
        plt.title('Twin Prime Scale Invariance (Logic Shock Strength)')
        plt.grid(True, which="both", ls="-", alpha=0.5)
        plt.legend()
        plt.savefig(save_path)
        print(f"📊 Prime resonance plot saved to {save_path}")
        plt.close()

if __name__ == "__main__":
    viz = GPUVisualizer()
    viz.plot_collatz_orbit(27) # The interesting one
    viz.plot_p_echo_stability(max_N=5000)
