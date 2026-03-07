import random

def hunt_counter_example(iterations=100, map_type="7n+1"):
    print(f"🚀 Hunting for GPU Escapees in {map_type}...")
    for _ in range(iterations):
        # Generate a random 60-bit "Chaotic Particle"
        n = random.getrandbits(60) | 1 # Ensure it's odd
        curr = n
        
        escaped = True
        for step in range(1, 500):
            if (curr - 8) % 10 == 0:
                escaped = False # Captured!
                break
            
            # Map Dynamics
            if map_type == "7n+1":
                curr = curr // 2 if curr % 2 == 0 else 7 * curr + 1
            else: # 3n-1
                curr = curr // 2 if curr % 2 == 0 else 3 * curr - 1
                
            if curr > 10**100: break # Infinity threshold

        if escaped:
            return f"🚨 FOUND REBEL: {n} escaped the +10 Gravity!"
    return "No rebels found. Gravity is holding... for now."

print(hunt_counter_example(500, "7n+1"))