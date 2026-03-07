-- Gpu/Core/GPU.lean: Main Library Entry
import Gpu.Core.Base.API
import Mathlib.Data.Nat.Factorization.Basic

namespace GPU

/--
The Radical of a number:
PROVEN: The product of distinct prime factors.
Implemented using Mathlib's verified Nat.primeFactors and prod.
-/
noncomputable def Radical (n : ℕ) : ℕ :=
  if n = 0 then 0 else (Nat.primeFactors n).prod id

end GPU
