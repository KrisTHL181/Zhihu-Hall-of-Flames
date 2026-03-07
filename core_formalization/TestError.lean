import Mathlib.Data.Real.Basic

namespace GPU.Test
theorem broken_logic : (1 : ℝ) < 0 := by
  linarith -- This MUST fail
end GPU.Test
