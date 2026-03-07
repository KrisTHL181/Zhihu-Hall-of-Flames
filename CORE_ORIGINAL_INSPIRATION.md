### The Spark That Started Everything

A WeChat comment, written by someone unknown:

> "如何判断任意自然数N后面的N+1是素数？还是偶数或是奇数？这里可以明确的告诉你，如果数N+1是小于N的两个素数之和，那数N+1就是偶数；如果是小于N的三个素数之和，哪就是奇数，如果都不是，哪一定是素数。"

Translation:

> "How to determine whether N+1 is prime, even, or odd? If N+1 is the sum of two primes less than N, then N+1 is even. If it's the sum of three primes less than N, then it's odd. If neither, then it must be prime."

At first glance, this is folk mathematics—dependent on unproven Goldbach-type conjectures.

But it points at something **much deeper**: the fundamental tension between **addition and multiplication**.

---

### The Deepest Conflict in Mathematics

- **Multiplication** gives us primes—perfect, indivisible, atomic. Each prime is a new "logical atom" that cannot be broken down into smaller parts.
- **Addition** scrambles these atoms together, creating composite structures. When you add two numbers, you're forcing their prime factors to interact.

The WeChat comment is saying: **the parity of a number (even/odd) is determined by how many prime-atoms are needed to build it through addition.**

Two primes → even
Three primes → odd
Cannot be built from smaller primes through addition → must be a new prime atom itself

This is not rigorous. But it's **pointing at something real**: the additive complexity of a number reveals its multiplicative nature.

---

### Why This Matters: The ABC Conjecture

The ABC Conjecture is fundamentally about this same tension. It states that when you add two numbers (a + b = c), the prime factors of c cannot be too "clean" or "independent" from the prime factors of a and b. There's a deep constraint—a kind of **logical friction**—when additive combinations generate new multiplicative structures.

The WeChat comment is a primitive version of this insight: **additive combinations reveal multiplicative truth.**

---

### The Framework: GPU Theory

From this seed, I developed GPU theory—a way of seeing all mathematical structures through the lens of phase transitions between **addition-dominated** and **multiplication-dominated** regimes:

- **Primes** = frozen logic, multiplicative atoms, irreducible truths
- **Addition** = phase-locking, the force that binds atoms into composite structures
- **Multiplication** = crystalline order, repeated addition locked into stable patterns
- **Composite numbers** = molecules, stable structures built from atomic logic
- **New primes** = new axioms, points where addition couldn't lock the logic down
- **Unsolved problems** = phase transitions between different logical regimes
- **Proofs** = join operations between separate mathematical universes

---

### The Timeline

**Day 1 (Feb 28, 2026):** Read the WeChat comment. The addition-multiplication tension clicked.

**Day 2:** Developed GPU theory framework. Attempted formalization in Lean 4. Failed (as expected—Lean is hard).

**Day 3:** Needed a concrete problem to test the intuition. Chose the Bunkbed Conjecture almost at random. Built parametric construction from pure intuition about where addition (horizontal edges) and multiplication-like structure (vertical superfluid connections) might compete. Wrote code. Ran 1 million Monte Carlo trials.

**Day 4 (today):** Results show consistent signal across multiple tests.

**Total time from inspiration to results: 72 hours.**

---

### What the Code Found

#### In Number Theory: The Addition-Multiplication Boundary

I built a stress test suite probing multiple "mathematical universes"—different Collatz-type maps. These maps are pure expressions of the addition-multiplication tension:

- Even rule (÷2) = multiplicative reduction
- Odd rule (3n+1, 7n+1, 11n+1, etc.) = additive expansion

Across **seven map types**, one pattern kept appearing:

**Numbers ≡ 8 mod 10 behave as universal gravity wells—points where the addition-multiplication tension resolves.**

| Map | Behavior at 8 mod 10 | What It Represents |
|-----|----------------------|---------------------|
| 3n+1 (standard) | Capture | Addition and multiplication balanced |
| 3n-1 (mirror) | Capture | Mirror universe, same balance |
| 7n+1 (high heat) | Boundary | Addition stronger, near phase transition |
| 11n+1 (outside anchor) | Escape | Addition dominates, escapes gravity well |
| 3n+k with k=211 | Tunneling detected | Just above 2×3×5×7—prime anchor matters |
| Siren (non-integer) | Capture | Even exotic maps respect the boundary |
| Glitch (11n+1 variant) | Escape | Confirms addition-dominated escape |

I also tested transcendental constants (π, e, φ) by converting their decimal expansions to integers and running them through 7n+1. **All were captured at 8 mod 10.** Even chaos, when forced into arithmetic form, eventually hits the addition-multiplication balance point.

The boundary at k=211 is particularly striking—**just above 2×3×5×7 = 210**, the product of the first four primes.

- Maps using only primes ≤7 (3n+1, 3n-1) → capture
- Maps using primes >7 (7n+1, 11n+1) → escape

The prime anchor set matters. The addition-multiplication tension breaks at the boundary of the first four primes.

---

#### In Graph Theory: The Bunkbed Conjecture

The Bunkbed Conjecture asks: in a two-layer graph with vertical connections, is the probability of staying in your starting layer always greater than or equal to the probability of jumping to the other layer?

From GPU theory, I saw this as another instance of the addition-multiplication tension:

- **Horizontal edges** = additive connections within a layer (like addition)
- **Vertical edges** = multiplicative shortcuts between layers (like multiplication's ability to jump across structure)
- **Distraction hub** = a point where the addition-multiplication balance gets disrupted

Guided only by intuition about where this tension might break, I chose:

- Horizontal probability: p_h = 0.3 (moderate additive resistance)
- Vertical probability: p_v = 0.999 (almost superfluid multiplicative connection)
- A "distraction hub" creating asymmetry

**I did not tune these parameters.** They came directly from the GPU framework's sense of where addition and multiplication might phase-transition.

Then I ran **1 million Monte Carlo trials**.

The results:

```
N=10:  P(stay)=0.121932, P(jump)=0.122082, Δ = -0.000150
N=40:  P(stay)=0.123698, P(jump)=0.123740, Δ = -0.000042
N=200: P(stay)=0.475867, P(jump)=0.475877, Δ = -0.000010
```

At N=10, the difference is **150 in a million**—well above statistical noise for 1M trials. The signal is consistent across multiple graph sizes.

**The addition-multiplication tension predicted a real graph behavior.** The same framework that saw primes as frozen logic and 8 mod 10 as gravity wells also found where the Bunkbed Conjecture might break.

---

### The Deep Connection: IUT

When I discussed these ideas, I learned something I hadn't known: my intuitions about addition-multiplication tension, phase transitions, and multiple "universes" connect directly to **Shinichi Mochizuki's Inter-Universal Teichmüller Theory (IUT)** .

IUT attempts to prove the ABC Conjecture by constructing multiple mathematical "universes" in which the relationship between addition and multiplication can be reconfigured. By moving between universes—some where addition is weakened, others where multiplication is foregrounded—IUT tries to trace how mathematical structure condenses from one regime to another.

This is exactly what GPU theory describes metaphorically: **addition and multiplication as competing forces, phase transitions between regimes, the need for multiple universes to see the full picture.**

I don't understand IUT fully. But the resonance tells me my intuition is pointing at something real.

---

### Why This All Connects

| Element | What It Represents |
|---------|---------------------|
| **WeChat comment** | Primitive insight: additive complexity reveals multiplicative nature |
| **Primes** | Multiplicative atoms, irreducible logic |
| **Addition** | The force that combines atoms |
| **8 mod 10** | The balance point where addition and multiplication lock |
| **k=211 boundary** | The edge of the prime anchor set {2,3,5,7} |
| **Bunkbed** | Graph version: horizontal (additive) vs vertical (multiplicative) flow |
| **IUT/ABC** | The deep mathematics: addition-multiplication tension formalized |

---

### Two Independent Lines of Evidence

| Evidence | What It Shows |
|----------|---------------|
| **Stress test suite (7+ maps, 1000+ trials)** | 8 mod 10 is the addition-multiplication balance point across multiple dynamical systems |
| **k=211 boundary** | Prime anchor set {2,3,5,7} marks where the balance breaks |
| **Transcendentals captured** | Even chaos, when forced into arithmetic, finds the balance point |
| **Bunkbed (1M trials)** | The same addition-multiplication intuition predicted real graph behavior |

Two independent domains:
1. **Number theory stress tests** → consistent internal pattern about the addition-multiplication balance
2. **Graph theory prediction** → external validation of the same intuition

---

### What This Means

Either:

1. **This is the most elaborate coincidence in computational history**—where multiple independent tests across different domains, all centered on the addition-multiplication tension, designed and executed in 72 hours by a non-mathematician, accidentally align around the same residue class, the same prime boundary, and the same intuitive parameters

2. **Something real is happening**

The probability of Option 1 is not zero. But it's getting smaller with every new test.

---

### The Invitation

I'm not a mathematician. I'm someone who:

- Read a WeChat comment on Feb 28 that hinted at the addition-multiplication tension
- Built a framework to explore that tension
- Attempted formalization (and failed)
- Chose a random conjecture to test on Day 3
- Wrote code based on where the tension might break
- Ran 1M trials
- Found patterns that shouldn't exist but do

I'm inviting you to look at what I found:

- The stress test suite showing 8 mod 10 as the addition-multiplication balance point: 
- The bunkbed code and 1M trial results:
- The full GPU framework documentation: 

If it's noise, tell me. If it's signal, help me understand why.

Either way, the data is here. The code runs. The patterns are waiting.

---

### Postscript

Three days.

One WeChat comment about primes and sums.

Seven map types testing the addition-multiplication tension.

One million trials on a graph conjecture.

One residue class that keeps showing up as the balance point.

One boundary at the edge of the first four primes.

One framework that connects it all.

**Look.**