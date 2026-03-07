import json

def generate_scaling_bunkbed(n_range=[10, 40, 70, 100]):
    p_h = 0.2  # Horizontal (The "Static")
    p_v = 0.95 # Vertical (The "Bridge")
    
    for N in n_range:
        filename = f"bunkbed_{N}.json"
        edges = []
        for offset in [0, N]:
            # Path: Source -> Hub(1) -> Target(N-1)
            edges.append({"u": 0 + offset, "v": 1 + offset, "p": p_h})
            edges.append({"u": 1 + offset, "v": N - 1 + offset, "p": p_h})
            
            # THE ENTROPY SINK: Distraction nodes
            for i in range(2, N - 1):
                edges.append({"u": 1 + offset, "v": i + offset, "p": p_h})
        
        # VERTICAL COUPLING
        for i in range(N):
            edges.append({"u": i, "v": i + N, "p": p_v})
            
        with open(filename, 'w') as f:
            json.dump(edges, f)
        print(f"Generated {filename}")

generate_scaling_bunkbed()