-- Gpu/Core/Decadic/Definitions.lean: Decadic Metric and Base-10 Harmonic Definitions
import Mathlib.Data.Real.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace GPU.Decadic

/--
The Decadic Metric (also called "The Grip"):
A potential function that measures proximity to the crystalline anchors n ≡ 8 (mod 10).
-/
noncomputable def metric (n : ℕ) : ℝ :=
  let residue := (n % 10 : ℤ)
  let dist := min (abs (residue - 8)) (abs (residue + 2))
  1.0 / ((dist : ℝ) + 1.0)

/--
The set of decadic anchors: {n | n ≡ 8 mod 10}
These are the "crystalline points" in the GPU lattice.
-/
def is_anchor (n : ℕ) : Prop := n % 10 = 8

end GPU.Decadic
