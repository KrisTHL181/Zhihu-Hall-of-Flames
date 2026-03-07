import math

def test_map_gravity(n_start, map_type="3n+1"):
    curr = n_start
    path = [curr]
    
    # Define the Map Dynamics
    for step in range(1, 2000):
        # Check for Decadic Capture (Residue 8 mod 10)
        if (curr - 8) % 10 == 0:
            capture_step = step
            # Calculate Local Gravity: G = ln(n) / steps
            # (Simplified version of your GPU Law)
            g_local = math.log(n_start) / capture_step
            return capture_step, g_local
            
        if map_type == "3n+1":
            curr = curr // 2 if curr % 2 == 0 else 3 * curr + 1
        elif map_type == "5n+1":
            curr = curr // 2 if curr % 2 == 0 else 5 * curr + 1
        elif map_type == "Syracuse":
            # Syracuse shortcut: (3n+1)/2^k
            if curr % 2 != 0:
                temp = 3 * curr + 1
                k = 0
                while temp % 2 == 0:
                    temp //= 2
                    k += 1
                curr = temp
            else:
                curr //= 2
        path.append(curr)
    return None, None

# Test Particle: Titan Scale (2^61 - 1)
n_titan = 2305843009213693951

maps = ["3n+1", "5n+1", "Syracuse"]
print(f"🔬 Testing Universal Gravity for n = 2^61 - 1\n" + "="*45)

for m in maps:
    step, g = test_map_gravity(n_titan, m)
    if step:
        print(f"Map: {m:10} | Capture Step: {step:4} | Calculated G: {g:.4f}")
    else:
        print(f"Map: {m:10} | FAILED TO CAPTURE (Escaped to Infinity?)")