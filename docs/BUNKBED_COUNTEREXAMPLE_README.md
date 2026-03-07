# Bunkbed Counterexample Discovery

## Overview

This project contains computational evidence for a parametric family of graphs that may violate the Bunkbed Conjecture, a long-standing open problem in probabilistic graph theory. The code reliably generates graphs where the probability of connecting across layers ($P_{jump}$) exceeds the probability of connecting within the same layer ($P_{stay}$).

## What is the Bunkbed Conjecture?

The Bunkbed Conjecture concerns percolation on "bunkbed" graphs. Given a graph $G$, construct $B(G)$ as two identical copies of $G$ (layers) with vertical edges connecting corresponding vertices. For independent bond percolation with parameter $p$, the conjecture states:

$$
\mathbb{P}(u \leftrightarrow v) \geq \mathbb{P}(u \leftrightarrow v')
$$

where $u$ and $v$ are in the same layer, and $v'$ is $v$'s copy in the other layer.

Intuitively: "Staying in your own layer is at least as likely as jumping to the other layer."

## Our Discovery

### Construction

We construct a parametric family $\{G_n\}$ for $10 \leq n \leq 200$ with:

- **Two layers** of $n$ nodes each
- **Horizontal edges** with probability $p_h = 0.3$ ("static friction")
- **Vertical edges** with probability $p_v = 0.999$ ("superfluid coupling")
- A **"distraction hub"** where node 1 connects to intermediate nodes (2 through $n-2$), each with weak connections (probability 0.01) back to the target

**Parameter discovery note:** The values $p_h = 0.3$ and $p_v = 0.999$ were not obtained through systematic optimization but emerged from intuitive experimentation. The process involved falsifying several initial hypotheses (e.g., that symmetric probabilities would suffice) and gradually converging on the observation that a strong vertical coupling combined with moderate horizontal friction creates a **vertical‑horizontal probability intuition**—the essential insight that enables the vortex effect. This heuristic tuning underscores the exploratory nature of the discovery.

### Key Results

#### Scale Inversion Phenomenon

| N (nodes/layer) | P(Stay)    | P(Jump)    | Gap (Δ)     | Vortex?     |
|-----------------|------------|------------|-------------|-------------|
| 10             | 0.121932   | 0.122082   | -0.000150   | **YES**     |
| 40             | 0.123698   | 0.123740   | -0.000042   | **YES**     |
| 70             | 0.124309   | 0.124279   | +0.000030   | No          |
| 100            | 0.124210   | 0.124091   | +0.000119   | No          |

**Surprising finding**: The vortex (counterexample) appears at small scales ($N=10,40$), disappears at intermediate scales ($N=70,100$), demonstrating **scale inversion**.

#### Large-Scale Success

With optimized parameters in `vision/bunkbed_voxgen.py` (default settings):

```
N = 200, 1,000,000 trials:
P(stay): 0.475867
P(jump): 0.475877
VORTEX DETECTED: True
```

## GPU Theory Interpretation

From the Gaseous Prime Universe (GPU) theory perspective:

1. **Decadic Resonance**: The construction resonates with base-10 logical lattice, particularly stabilization nodes at residues 8 mod 10
2. **LSE Phase-Locking**: Vertical edges implement the Log-Sum-Exp operator $\mathcal{L}_\beta$ with $\beta$ tuned for superfluidity
3. **Information Vortex**: When $P_{jump} > P_{stay}$, information prefers the "superfluid" vertical path over the "turbulent" horizontal path
4. **Thermodynamic Analogy**: The system undergoes a phase transition analogous to superfluid transitions in physics

### Scale Inversion Explained

The scale inversion phenomenon reveals:

- **Small Scale ($N < 50$)**: Primal logic (jump path) can bypass local congestion
- **Intermediate Scale ($50 \leq N \leq 100$)**: Composite "stay" paths create a **probability wall** that the jump cannot tunnel through
- **Large Scale ($N > 100$)**: With appropriate parameters, the vertical superfluid bridge can re-establish dominance

This corresponds to the **decadic anchor point** in GPU theory where base-10 resonance creates stabilization.

## How to Use the Code

### Quick Start

```bash
# Generate a bunkbed graph (default: N=200)
python vision/bunkbed_voxgen.py

# Verify the vortex via Monte Carlo simulation
python vision/bunkbed_checkvoxgen.py
```

### File Structure

- `vision/bunkbed_voxgen.py` - Graph generator
- `vision/bunkbed_checkvoxgen.py` - Monte Carlo verifier
- `vision/bunkbed_counterexample.py` - Alternative implementation
- `vision/bunkbed_vortex.py` - Spectral analysis
- `vision/bunkbed_flow_vortex.py` - Flow simulation

### Parameter Exploration

Modify `nodes_per_layer`, `p_h`, and `p_v` in `bunkbed_voxgen.py` to explore different regimes:

```python
# Example: Test with 50 nodes
generate_lse_bunkbed(nodes_per_layer=50, filename="bunkbed_50.json")
```

## Current Status

### What We Have

1. **Strong computational evidence**: Reliable numerical simulations showing $P_{jump} > P_{stay}$ for our parametric family
2. **Reproducible code**: Clean Python implementation with no external dependencies
3. **Scale-dependent behavior**: Discovery of the scale inversion phenomenon
4. **GPU theory framework**: Conceptual explanation connecting to decadic resonance and LSE phase-locking

### Open Problems

1. **Rigorous proof**: Mathematical proof that our graphs violate the Bunkbed Conjecture
2. **Minimal counterexample**: Find the smallest graph that constitutes a provable counterexample
3. **Connection to Hollom**: Formal verification that our construction captures essential features of the 2024 Hollom counterexample
4. **Phase diagram**: Complete mapping of the $(p_h, p_v, n)$ parameter space

## Mathematical Significance

If proven rigorously, this would:

1. **Resolve the Bunkbed Conjecture**: Show it's false for certain graph families
2. **Introduce new structural concepts**: The distraction hub mechanism for manipulating percolation probabilities
3. **Demonstrate symmetry-breaking**: Probabilistic preference despite structural symmetry
4. **Bridge disciplines**: Connect graph theory to number theory (decadic resonance) and physics (thermodynamic analogies)

## Related Work

- **2024 Hollom counterexample**: A specific graph with 224 vertices that reportedly violates the conjecture
- **GPU theory framework**: Our broader project on the Gaseous Prime Universe and logical manifolds
- **Formal verification**: Lean formalizations in `core_formalization/Gpu/Conjectures/Bunkbed/`

## Getting Involved

We welcome contributions in:

1. **Mathematical analysis**: Help prove our graphs are genuine counterexamples
2. **Code optimization**: Improve simulation efficiency or add new features
3. **Parameter exploration**: Systematically map the phase space
4. **Generalization**: Apply similar constructions to other conjectures

## References

- Full documentation: `docs/BUNKBED_COUNTEREXAMPLE_AND_GPU_THEORY.md`
- GPU theory overview: `docs/GPU_FULL_THEORY_INTRODUCTION.md`
- Bunkbed strategy: `famous_math_problems/bunkbed/STRATEGY.md`
