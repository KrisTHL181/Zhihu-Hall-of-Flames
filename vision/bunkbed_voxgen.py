import json

def generate_lse_bunkbed(nodes_per_layer=70, filename="bunkbed.json"):
    p_h = 0.3      # Horizontal "Static"
    p_v = 0.999    # Vertical "Coupling" (High LSE pressure)
    
    stay_target = nodes_per_layer - 1
    jump_target = (2 * nodes_per_layer) - 1
    
    edges = []
    for offset in [0, nodes_per_layer]:
        # Path: 0 -> 1 -> Target
        edges.append({"u": 0 + offset, "v": 1 + offset, "p": p_h})
        edges.append({"u": 1 + offset, "v": stay_target + offset, "p": p_h})
        
        # LSE GADGET: The "Distraction Hub"
        # We connect Node 1 to a "Bus" (Nodes 2-68)
        # In Layer 1, this "bleeds" the signal.
        for i in range(2, nodes_per_layer - 1):
            edges.append({"u": 1 + offset, "v": i + offset, "p": p_h})
            # CROSS-TALK: Connect the bus back to the Target
            # This creates "Parallel Interference"
            edges.append({"u": i + offset, "v": stay_target + offset, "p": 0.01})
            
    # THE VERTICAL SUPER-POSITION (The LSE Bridge)
    for i in range(nodes_per_layer):
        edges.append({"u": i, "v": i + nodes_per_layer, "p": p_v})

    with open(filename, 'w') as f:
        json.dump(edges, f)

generate_lse_bunkbed(nodes_per_layer=100)