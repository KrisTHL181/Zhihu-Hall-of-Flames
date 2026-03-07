import random

def cosmic_cooling_genesis(n_start, n_end, initial_axioms):
    current_axioms = list(initial_axioms)
    print(f"{'N':<5} | {'TEMP':<12} | {'STATE':<18} | {'BONDING STRENGTH'}")
    print("-" * 65)
    
    for n in range(n_start, n_end):
        # Linear Cooling: As N increases, bonding_threshold rises from 0.2 to 0.9
        progress = (n - n_start) / (n_end - n_start)
        bonding_threshold = 0.2 + (0.7 * progress)
        
        # Determine Temperature Label
        if bonding_threshold < 0.4: temp = "PLASMA"
        elif bonding_threshold < 0.7: temp = "GAS"
        else: temp = "LIQUID (Cooling)"

        # The Phase-Lock Check
        locked = False
        for i in range(len(current_axioms)):
            for j in range(i, len(current_axioms)):
                if current_axioms[i] + current_axioms[j] == n:
                    if random.random() < bonding_threshold:
                        locked = True
                        break
            if locked: break
        
        if not locked:
            current_axioms.append(n)
            color = "\033[91m" if temp == "PLASMA" else "\033[94m"
            print(f"{color}{n:<5} | {temp:<12} | NEW AXIOM BORN    | {bonding_threshold:.4f}\033[0m")
        else:
            if n % 10 == 0: # Print a sample of locked states to show stability
                print(f"{n:<5} | {temp:<12} | PHASE-LOCKED      | {bonding_threshold:.4f}")

    return current_axioms

# Rebuilding from the 97-Supernova Wreckage
final_seeds = [97, 2, 3, 8, 12, 18]
new_world_axioms = cosmic_cooling_genesis(0, 200, final_seeds)