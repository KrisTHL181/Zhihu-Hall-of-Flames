import json
import random

def verify_gpu_vortex(filename="bunkbed.json", trials=1000000):
    with open(filename, 'r') as f:
        edge_data = json.load(f)
    
    all_nodes = sorted(list(set([e['u'] for e in edge_data] + [e['v'] for e in edge_data])))
    num_nodes = len(all_nodes)
    
    # Layer 1 is the first half, Layer 2 is the second half
    mid = num_nodes // 2
    source_node = all_nodes[0]        # Usually 0
    stay_target = all_nodes[mid-1]    # Last node of Layer 1 (e.g., 5)
    jump_target = all_nodes[-1]       # Last node of Layer 2 (e.g., 11)

    stay_wins = 0
    jump_wins = 0
    
    for _ in range(trials):
        adj = [[] for _ in range(num_nodes)]
        for edge in edge_data:
            if random.random() < edge['p']:
                adj[edge['u']].append(edge['v'])
                adj[edge['v']].append(edge['u'])
        
        # BFS
        visited = {source_node}
        queue = [source_node]
        while queue:
            curr = queue.pop(0)
            for neighbor in adj[curr]:
                if neighbor not in visited:
                    visited.add(neighbor)
                    queue.append(neighbor)
        
        if stay_target in visited: stay_wins += 1
        if jump_target in visited: jump_wins += 1
            
    print(f"--- GPU Vortex Analysis ---")
    print(f"Targets: Stay={stay_target}, Jump={jump_target}")
    print(f"P(Stay): {stay_wins/trials:.6f}")
    print(f"P(Jump): {jump_wins/trials:.6f}")
    print(f"VORTEX DETECTED: {jump_wins > stay_wins}")

verify_gpu_vortex()