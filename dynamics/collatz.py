def analyze_collatz_viscosity(n, synthetic_axioms):
    path = [n]
    viscosity_score = 0
    temp = n
    
    while temp != 1:
        if temp % 2 == 0:
            temp //= 2
        else:
            temp = 3 * temp + 1
        
        # If the path hits a Synthetic Axiom or its Decadic Harmonic (+10)
        if temp in synthetic_axioms or (temp > 10 and (temp - 8) % 10 == 0):
            viscosity_score += 1
        
        path.append(temp)
        if len(path) > 1000: break
    
    return {
        "start": n,
        "length": len(path),
        "peak": max(path),
        "viscosity_score": viscosity_score
    }

# Synthetic Axioms from our Genesis 2.0: [2, 3, 8, 12, 18, 22, 28, 32, 38, 42, 48]
axioms = [2, 3, 8, 12, 18, 22, 28, 32, 38, 42, 48]

results_12 = analyze_collatz_viscosity(12, axioms)
results_27 = analyze_collatz_viscosity(27, axioms)

print(f"SYNT-12: Length={results_12['length']}, Peak={results_12['peak']}, Viscosity={results_12['viscosity_score']}")
print(f"STD-27 : Length={results_27['length']}, Peak={results_27['peak']}, Viscosity={results_27['viscosity_score']}")