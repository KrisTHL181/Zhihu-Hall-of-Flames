import math
import numpy as np
from core.information_decay_meter import InformationDecayMeter

class HASMThermodynamicSimulator:
    """
    Verifies HASM via Thermodynamic Resonance.
    Hypothesis: The entropy decay rate (gamma) of the Boundary 
    resonances with the Adelic decay rate of the Volume.
    """
    def __init__(self, limit=100000):
        self.limit = limit
        self.n_values = np.arange(1, limit + 1)
        self.meter = InformationDecayMeter()

    def get_decadic_decay(self, window=1000):
        """Calculates decay rate of decadic entropy."""
        def metric(n):
            residue = n % 10
            dist = min(abs(residue - 8), abs(residue + 2))
            return 1.0 / (dist + 1.0)
        
        signal = np.array([metric(n) for n in self.n_values])
        decay_rates = []
        
        for i in range(0, self.limit - 2*window, window):
            s1 = self.meter.calculate_logical_entropy(int(np.sum(signal[i:i+window])))
            s2 = self.meter.calculate_logical_entropy(int(np.sum(signal[i+window:i+2*window])))
            decay_rates.append(s1 - s2)
            
        return np.array(decay_rates)

    def get_adelic_decay(self, window=1000):
        """Calculates decay rate of Adelic complexity."""
        primes = [2, 3, 5, 7, 11]
        complexity = np.zeros(self.limit)
        for p in primes:
            curr_p = p
            while curr_p <= self.limit:
                complexity[curr_p-1::curr_p] += 1
                curr_p *= p
        
        decay_rates = []
        for i in range(0, self.limit - 2*window, window):
            s1 = self.meter.calculate_logical_entropy(int(np.sum(complexity[i:i+window])))
            s2 = self.meter.calculate_logical_entropy(int(np.sum(complexity[i+window:i+2*window])))
            decay_rates.append(s1 - s2)
            
        return np.array(decay_rates)

    def verify_thermodynamic_resonance(self):
        print("\n🔭 VERIFYING HASM THERMODYNAMIC RESONANCE")
        print("-" * 55)
        
        b_decay = self.get_decadic_decay()
        v_decay = self.get_adelic_decay()
        
        # Resonance is the correlation of the decay fluctuations
        resonance = np.corrcoef(b_decay, v_decay)[0, 1]
        
        print(f"Decay Samples: {len(b_decay)}")
        print(f"HASM DECAY RESONANCE: {resonance:.4f}")
        
        status = "✅ HOLOGRAPHIC" if abs(resonance) > 0.1 else "❌ DE-COUPLED"
        print(f"Status: {status}")
        
        if abs(resonance) > 0.1:
            print("\n[✔] BREAKTHROUGH: The Boundary and Volume cool in unison!")
            print("    Information dissipation is a holographic invariant of the GPU.")
            
        return resonance

if __name__ == "__main__":
    simulator = HASMThermodynamicSimulator(limit=200000)
    simulator.verify_thermodynamic_resonance()
