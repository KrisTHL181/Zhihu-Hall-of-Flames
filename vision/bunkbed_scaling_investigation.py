import json
import random
import os

def verify_vortex_growth(trials=1000000):
    # Find all bunkbed files and sort them by N
    files = sorted([f for f in os.listdir() if f.startswith("bunkbed_") and f.endswith(".json")], 
                   key=lambda x: int(x.split('_')[1].split('.')[0]))
    
    print(f"{'N':<5} | {'P(Stay)':<10} | {'P(Jump)':<10} | {'Gap (Delta)':<12} | {'Vortex'}")
    print("-" * 60)

    for file in files:
        with open(file, 'r') as f:
            edges = json.load(f)
        
        n_total = max(max(e['u'], e['v']) for e in edges) + 1
        n_layer = n_total // 2
        source = 0
        target_stay = n_layer - 1
        target_jump = n_total - 1
        
        stay_count = 0
        jump_count = 0
        
        for _ in range(trials):
            # Adjacency check for the current trial
            adj = [[] for _ in range(n_total)]
            for e in edges:
                if random.random() < e['p']:
                    adj[e['u']].append(e['v'])
                    adj[e['v']].append(e['u'])
            
            # BFS for reachability
            visited = {source}
            queue = [source]
            found_stay = False
            found_jump = False
            
            while queue:
                curr = queue.pop(0)
                if curr == target_stay: found_stay = True
                if curr == target_jump: found_jump = True
                if found_stay and found_jump: break
                
                for neighbor in adj[curr]:
                    if neighbor not in visited:
                        visited.add(neighbor)
                        queue.append(neighbor)
            
            if found_stay: stay_count += 1
            if found_jump: jump_count += 1
            
        p_stay = stay_count / trials
        p_jump = jump_count / trials
        delta = p_stay - p_jump
        vortex = "DETECTED" if delta < 0 else "False"
        
        print(f"{n_layer:<5} | {p_stay:<10.6f} | {p_jump:<10.6f} | {delta:<12.6f} | {vortex}")

verify_vortex_growth()