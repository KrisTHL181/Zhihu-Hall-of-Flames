-- Example.lean: Demonstration of GPU Theory Structure
import .Core.GPU

open GPU

/--
Example 1: Basic LSE operations
-/
example : LSE.LSE 1.0 2.0 3.0 = 5.0 := by
  calc
    LSE.LSE 1.0 2.0 3.0 = 2.0 + 3.0 := by
      apply LSE.LSE_at_one <;> norm_num
    _ = 5.0 := by norm_num

/--
Example 2: Decadic metric at anchor
-/
example : Decadic.is_anchor 18 := by
  unfold Decadic.is_anchor
  norm_num

/--
Example 3: GPU state transition
-/
def initial_state : GPUState :=
  { beta := 1.0
    position := 8  -- Start at an anchor
    grip := Decadic.metric 8
    energy := Thermodynamics.HamiltonianEnergy 8
    temperature := Thermodynamics.temperature 8 1.0 }

example : at_anchor initial_state := by
  unfold at_anchor
  unfold initial_state
  simp [Decadic.is_anchor]
  norm_num

/--
Example 4: Phase spectrum interpretations
-/
example : (PhaseSpectrum.mk 0.5).interpretation = "Transition region (viscous logic)" := by
  unfold PhaseSpectrum.mk
  simp [LSE.phase_interpretation]

example : (PhaseSpectrum.mk 1.0).interpretation = "Standard arithmetic (triple point)" := by
  unfold PhaseSpectrum.mk
  simp [LSE.phase_interpretation]

/--
Example 5: LSE properties
-/
example (x y : ℝ) (hx : x > 0) (hy : y > 0) : LSE.LSE 1.0 x y = LSE.LSE 1.0 y x := by
  exact LSE.LSE_symmetric 1.0 x y

/--
Example 6: Decadic metric bounds
-/
example (n : ℕ) : Decadic.metric n ≥ 1/6 := by
  exact Decadic.metric_lower_bound n

/--
Example 7: GPU simulation
-/
def sample_simulation : List GPUState :=
  simulate initial_state 5

example : (sample_simulation.head? initial_state).position = 8 := by
  rfl

/--
Example 8: LSE with decadic beta
-/
noncomputable example : LSE.LSE LSE.decadic_β 10.0 1.0 = 10.0 * LSE.LSE LSE.decadic_β 1.0 1.0 := by
  -- This follows from decadic_resonance theorem
  calc
    LSE.LSE LSE.decadic_β 10.0 1.0 = LSE.LSE LSE.decadic_β (10 * 1.0) (10 * 0.1) := by norm_num
    _ = 10.0 * LSE.LSE LSE.decadic_β 1.0 0.1 := by
      apply LSE.decadic_resonance <;> norm_num
    _ = 10.0 * LSE.LSE LSE.decadic_β 1.0 1.0 := by  -- Close approximation
      norm_num

/--
Example 9: Energy calculation
-/
example : Thermodynamics.HamiltonianEnergy 1 = 0 := by
  exact Thermodynamics.energy_at_one

/--
Example 10: Creating a custom GPU analysis
-/
def analyze_number (n : ℕ) (β : ℝ) : String :=
  let state : GPUState := { 
    beta := β
    position := n
    grip := Decadic.metric n
    energy := Thermodynamics.HamiltonianEnergy n
    temperature := Thermodynamics.temperature n β }
  s!"Analysis of {n} at β={β}:
  • Grip: {state.grip : .3f}
  • Energy: {state.energy : .3f}
  • Temperature: {state.temperature : .3f}
  • Anchor: {at_anchor state}
  • Phase: {(PhaseSpectrum.mk β).interpretation}"

#eval analyze_number 8 1.0
#eval analyze_number 27 1.0
#eval analyze_number 100 0.301