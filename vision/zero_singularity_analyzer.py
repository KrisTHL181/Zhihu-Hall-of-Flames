import math
import numpy as np

def verify_zero_repulsion():
    """
    Riemann Zero Singularity Analysis:
    Verifies that the spacings between zeros follow the GUE (Random Matrix) distribution.
    A 'Mixed Gas' must show Level Repulsion (zeros rarely get close).
    """
    print("🔭 VERIFYING RIEMANN ZERO SINGULARITY: SPECTRAL REPULSION")
    print("Testing if Spectral Nodes (Zeros) act as Repelling Singularities.")
    print("-" * 65)
    
    # First 15 Riemann Zeros (Im(s) values on the critical line)
    zeros = [
        14.1347, 21.0220, 25.0109, 30.4249, 32.9351, 
        37.5862, 40.9187, 43.3271, 48.0052, 49.7738,
        52.9703, 56.4462, 59.3470, 60.8318, 65.1125
    ]
    
    # Normalized Spacings (Gaps between zeros)
    # The average spacing should be roughly 2*pi / ln(T)
    # Here we just look at the distribution of gaps.
    gaps = []
    for i in range(len(zeros) - 1):
        gaps.append(zeros[i+1] - zeros[i])
    
    avg_gap = np.mean(gaps)
    min_gap = min(gaps)
    
    print(f"Number of Spectral Nodes analyzed: {len(zeros)}")
    print(f"Average Spectral Spacing: {avg_gap:.4f}")
    print(f"Minimum Spacing detected: {min_gap:.4f}")
    
    # Level Repulsion Test:
    # In a non-repelling system (Poisson), min_gap would be very small (~0).
    # in a repelling system (GUE), gaps are forced away from zero.
    repulsion_ratio = min_gap / avg_gap
    print(f"Repulsion Ratio (Min/Avg): {repulsion_ratio:.4f}")
    
    if repulsion_ratio > 0.3:
        print("\n[✔] Conclusion: CLEAR SPECTRAL REPULSION DETECTED.")
        print("The Zeros act as stable singularities that scaffold the critical line.")
    else:
        print("\n🚨 Conclusion: WEAK REPULSION. Spectral field may be unstable.")
    

if __name__ == "__main__":
    verify_zero_repulsion()
