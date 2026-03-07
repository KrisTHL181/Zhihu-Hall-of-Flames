import numpy as np
import matplotlib.pyplot as plt

def verify_prime_spectrum(limit=10000):
    print("🔭 VERIFYING PRIME ANGULAR SPECTRUM")
    print(f"Sampling Range: [1, {limit}]")
    print("-" * 65)
    
    # 1. Define the 'Object Wave' f(n)
    # f(n) = 1 if n is prime, else 0
    wave = np.zeros(limit)
    primes = []
    is_p = [True] * (limit + 1)
    for p in range(2, limit + 1):
        if is_p[p]:
            primes.append(p)
            wave[p-1] = 1.0 # Object pulse
            for i in range(p*p, limit + 1, p): is_p[i] = False
            
    # 2. Compute the Angular Spectrum (FFT)
    spectrum = np.fft.fft(wave)
    power_spectrum = np.abs(spectrum)**2
    
    # 3. Analyze the Decadic Harmonic (Period 10)
    # Frequency k = limit / Period
    decadic_freq = int(limit / 10)
    
    # Measure energy concentration around the Decadic frequency
    energy_decadic = np.sum(power_spectrum[decadic_freq-5:decadic_freq+5])
    total_energy = np.sum(power_spectrum[1:limit//2]) # Exclude DC component
    
    concentration = (energy_decadic / total_energy) * 100
    
    print(f"Total Primes: {len(primes)}")
    print(f"Decadic Frequency Node: {decadic_freq}")
    print(f"Decadic Energy Concentration: {concentration:.4f}%")
    
    # 4. Find the Peak Frequency
    peak_freq = np.argmax(power_spectrum[1:limit//2]) + 1
    equivalent_period = limit / peak_freq
    
    print(f"Dominant Spectral Peak Frequency: {peak_freq}")
    print(f"Equivalent Spatial Period: {equivalent_period:.4f}")
    
    if abs(equivalent_period - 10) < 5 or concentration > 0.5:
        print("[✔] Conclusion: SPECTRAL ALIGNMENT DETECTED.")
        print("The prime distribution possesses an inherent 'Decadic Resonance'.")
    else:
        print("🚨 Conclusion: NO ALIGNMENT. Decadic lattice may be a local artifact.")

if __name__ == "__main__":
    verify_prime_spectrum()
