import math
import matplotlib.pyplot as plt

def run_tensor_sink(n_start, steps=500):
    n = n_start
    path_n = [n]
    ages = list(range(steps))
    captured = False
    
    # P4 Anchor for temporal resonance
    P4 = 210 
    
    for t in range(1, steps):
        # The Axiomatic Check (Base Gravity)
        if (n - 8) % 10 == 0:
            # In a Tensor sink, capture isn't instant. 
            # The "Age" must also align.
            if t % 5 == 0: 
                captured = True
                return path_n, t, "TENSOR CAPTURE"
        
        # 3rd-Order Dynamics: Multiplier varies with Time (t)
        # M fluctuates slightly around 3
        m_tensor = 3 + 0.5 * math.sin(t * math.pi / 20)
        
        if n % 2 == 0:
            n = n // 2
        else:
            # The Tensor force
            n = int(m_tensor * n + 1)
            
        path_n.append(n)
        if n > 10**100: return path_n, t, "DIVERGENCE"
        
    return path_n, steps, "STABLE TENSOR ORBIT"

# Test the Titan
n_titan = 2**61 - 1
path, end_step, status = run_tensor_sink(n_titan)

print(f"🔬 Tensor Sink Analysis | Status: {status}")
print(f"Final Step: {end_step} | Final Value Length: {len(str(path[-1]))} digits")