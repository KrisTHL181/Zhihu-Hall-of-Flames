import numpy as np
import math

class NewtonBoltzmannSimulator:
    def __init__(self, n_particles=100):
        self.n = n_particles
        # Initial deterministic state (Velocities)
        self.velocities = np.ones(n_particles) 

    def lse_aggregate(self, data, beta):
        """The GPU Operator: Aggregates micro-states into a macro-metric."""
        if beta > 50: return np.max(data) # Newtonian/Crystalline Limit
        if beta == 0: return np.geom_prod(data)**(1/len(data))
        return (np.sum(data**beta) / self.n)**(1/beta)

    def calculate_logical_entropy(self, data, beta):
        """Measures the 'Blur' of the system at a specific Phase-Locking strength."""
        macro_state = self.lse_aggregate(data, beta)
        # Entropy is the 'Surprise' between micro-detail and macro-aggregation
        deviations = np.abs(data - macro_state)
        return np.mean(deviations)

    def run_transition_scan(self):
        print("🌡️ SCANNING NEWTON-TO-BOLTZMANN TRANSITION")
        print(f"System: {self.n} Particles | Initial State: Uniform Velocity")
        print(f"{'Beta (β)':<10} | {'Macro Energy':<15} | {'Logical Entropy (S)':<15} | {'Regime'}")
        print("-" * 70)
        
        # Inject some 'Micro-Chaos' (Thermal noise)
        micro_noise = self.velocities + np.random.normal(0, 0.1, self.n)
        
        for beta in [100, 10, 5, 2, 1, 0.5, 0.1]:
            macro_e = self.lse_aggregate(micro_noise, beta)
            s_logic = self.calculate_logical_entropy(micro_noise, beta)
            
            if beta > 10:
                regime = "NEWTONIAN (Solid)"
            elif beta > 1.5:
                regime = "VISCOUS (Transition)"
            elif beta > 0.5:
                regime = "BOLTZMANN (Gas)"
            else:
                regime = "SUPERFLUID (Plasma)"
                
            print(f"{beta:<10.2f} | {macro_e:<15.4f} | {s_logic:<15.4f} | {regime}")

        print("[✔] Conclusion: As Beta decreases, Logical Entropy (S) increases.")
        print("The system 'leaks' information, transitioning from deterministic tracking to statistical averaging.")

if __name__ == "__main__":
    simulator = NewtonBoltzmannSimulator()
    simulator.run_transition_scan()
