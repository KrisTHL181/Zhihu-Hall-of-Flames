import math

def gpu_sabotage_test(n_start, axioms):
    path = [n_start]
    curr = n_start
    
    print(f"🚀 Launching Sabotage Test for n = {n_start}...")
    
    while curr != 1 and len(path) < 2000:
        curr = curr // 2 if curr % 2 == 0 else 3 * curr + 1
        path.append(curr)
        
        # Check if it hits the +10 "Gravity Well"
        if (curr - 8) % 10 == 0:
            print(f"📍 CAPTURED! Number hit Decadic Node {curr} at step {len(path)}")
            break
            
    return path

# We use a number that is 'far' from the 8-resonance in modular space
# Example: 2**31 - 1 (A large prime Mersenne number)
axioms = {2, 3, 8, 12, 18, 22, 28, 32, 38, 42, 48}
test_path = gpu_sabotage_test(2147483647, axioms)