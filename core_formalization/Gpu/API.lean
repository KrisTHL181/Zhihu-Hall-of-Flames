-- Core/LSE/API.lean: Public Interface for LSE Phase-Locking Operator
import Gpu.Definitions
-- import Gpu.Theorems  -- Temporarily commented until fixed

namespace GPU.LSE

/--
Public API for the LSE Phase-Locking Operator.
This module exports all definitions and theorems needed by other parts of the GPU theory.
-/

-- Export main definition
export Definitions (LSE)

-- Export fundamental theorems
export Definitions (LSE_at_one LSE_at_zero_limit LSE_monotone_in_beta 
                    LSE_symmetric LSE_homogeneous LSE_bounds decadic_β decadic_β_value)

-- Export advanced theorems from Theorems.lean
-- (These will be added as we prove them)

/--
Convenience function: LSE addition (β = 1)
-/
def add (x y : ℝ) : ℝ := LSE 1.0 x y

/--
Convenience function: LSE multiplication limit (β → 0)
Note: This is the limit, not exact value for β=0.
-/
noncomputable def mul_limit (x y : ℝ) : ℝ := x * y

/--
Phase-locking coefficient interpretation:
- β < 0: Not physically meaningful in GPU (would give complex results)
- β = 0: Multiplicative universe (superfluid limit)
- 0 < β < 1: Transition region (viscous logic)
- β = 1: Standard arithmetic universe (triple point)
- β > 1: Crystalline universe (selection/max operator limit)
-/
def phase_interpretation (β : ℝ) : String :=
  if β < 0 then "Non-physical (complex phase)"
  else if β = 0 then "Multiplicative universe (superfluid)"
  else if β < 1 then "Transition region (viscous logic)"
  else if β = 1 then "Standard arithmetic (triple point)"
  else "Crystalline universe (selection limit)"

/--
Special β values used in GPU theory:
1. β = 0.3010... (decadic harmonic)
2. β = 1.0 (standard arithmetic)
3. β = ∞ (max operator limit)
-/
structure SpecialBetaValues where
  decadic : ℝ := decadic_β
  standard : ℝ := 1.0
  crystalline : ℝ := 100.0  -- Approximation of ∞

/--
Create LSE operator with automatic positivity check.
Returns 0 if either input is non-positive (logical vacuum).
-/
def LSE_safe (β : ℝ) (x y : ℝ) : ℝ :=
  if x > 0 ∧ y > 0 then LSE β x y else 0

/--
LSE operator for natural numbers (coerced to ℝ).
Useful for number-theoretic applications.
-/
def LSE_nat (β : ℝ) (m n : ℕ) : ℝ :=
  LSE β (m : ℝ) (n : ℝ)

end GPU.LSE