import cmath
import math

def complex_gpu_stress_test(real_part, imag_part):
    # Initialize the Complex Particle
    z = complex(real_part, imag_part)
    path = [z]
    
    print(f"🌀 Launching Complex Particle: z = {z}")
    print(f"Initial Magnitude: {abs(z):.2e}")
    
    captured = False
    for step in range(1, 1500):
        # The Complex Collatz Flow
        # We apply the transformation to the magnitude-dominant logic
        if int(abs(z)) % 2 == 0:
            z = z / 2
        else:
            z = 3 * z + 1
            
        path.append(z)
        
        # GPU Capture Logic: Does the REAL part hit the +10 Node?
        # We look for the 'Real-Axis Grounding'
        if abs(z.imag) < 1e-6: # Imaginary component has evaporated
             if (int(z.real) - 8) % 10 == 0:
                print(f"📍 CAPTURED on Real Axis at step {step}")
                print(f"Final Value: {z.real}")
                captured = True
                break
        
        # Check for 'Orbital Snaring' (Real part hits 8 even with Imaginary tail)
        if (int(z.real) - 8) % 10 == 0 and not captured:
            print(f"💫 ORBITAL SNARLING at step {step}")
            print(f"Z-State: {z}")
            # We don't break yet, we want to see if the Imaginary part 'cools'
            
    return path

# Running the 2^31 Sabotage in Complex Space
# We start with equal Real and Imaginary 'Energy'
n_val = 2147483647 
complex_path = complex_gpu_stress_test(n_val, n_val)