import numpy as np
import math

class LawGeneralizer:
    def __init__(self, x=10, y=20):
        self.x = x
        self.y = y
        # Contradicting Facts: Addition and Multiplication
        self.fact_add = x + y
        self.fact_mul = x * y

    def lse_op(self, beta):
        if beta == 0: return self.x * self.y
        return (self.x**beta + self.y**beta)**(1/beta)

    def measure_unification_entropy(self, beta):
        """
        Measures the 'Surprise' (Entropy) of representing 
        both facts using a single LSE operator at a specific Beta.
        """
        prediction = self.lse_op(beta)
        # Difference between the 'Unifying Operator' and the 'Contradicting Facts'
        err_add = abs(prediction - self.fact_add)
        err_mul = abs(prediction - self.fact_mul)
        
        # Combined Surprise (Normalized)
        total_surprise = (err_add + err_mul) / (self.fact_add + self.fact_mul)
        return total_surprise

    def generalize(self):
        print(f"🧠 GENERALIZING LAWS: Unifying Addition and Multiplication")
        print(f"Inputs: x={self.x}, y={self.y}")
        print(f"{'Beta (β)':<10} | {'Unified Prediction':<20} | {'Surprise (S)'}")
        print("-" * 55)
        
        best_beta = 0
        min_surprise = float('inf')
        
        # Search for the Minimum Entropy Beta
        for beta in np.linspace(0, 1, 11):
            surprise = self.measure_unification_entropy(beta)
            prediction = self.lse_op(beta)
            
            if surprise < min_surprise:
                min_surprise = surprise
                best_beta = beta
                
            print(f"{beta:<10.1f} | {prediction:<20.4f} | {surprise:.4f}")
            
        print(f"[✔] UNIVERSAL LAW DISCOVERED at β={best_beta}")
        print(f"This is the point of Minimum Entropy Unification.")

if __name__ == "__main__":
    generalizer = LawGeneralizer()
    generalizer.generalize()
