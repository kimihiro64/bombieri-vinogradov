import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Complex.RemovableSingularity

/-!
# Entire divided differences

This module removes the apparent singularity in `(f(z) - f(c)) / (z - c)` for an entire function.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

noncomputable def entireDividedDifference (f : ℂ → ℂ) (c : ℂ) : ℂ → ℂ :=
  Function.update (fun z ↦ (f z - f c) / (z - c)) c (deriv f c)

theorem entireDividedDifference_apply_of_ne (f : ℂ → ℂ) {c z : ℂ} (hz : z ≠ c) :
    entireDividedDifference f c z = (f z - f c) / (z - c) := by
  rw [entireDividedDifference, Function.update_of_ne hz]

theorem entireDividedDifference_differentiableAt_of_ne (f : ℂ → ℂ) {c z : ℂ}
    (hf : Differentiable ℂ f) (hz : z ≠ c) :
    DifferentiableAt ℂ (entireDividedDifference f c) z := by
  apply DifferentiableAt.congr_of_eventuallyEq
  · have hconst : DifferentiableAt ℂ (fun _ : ℂ ↦ f c) z := by fun_prop
    have hden : DifferentiableAt ℂ (fun w : ℂ ↦ w - c) z := by fun_prop
    exact ((hf z).sub hconst).div hden (sub_ne_zero.mpr hz)
  · filter_upwards [eventually_ne_nhds hz] with w hw
    exact entireDividedDifference_apply_of_ne f hw

theorem entireDividedDifference_differentiable (f : ℂ → ℂ) (c : ℂ)
    (hf : Differentiable ℂ f) :
    Differentiable ℂ (entireDividedDifference f c) := by
  intro z
  rcases eq_or_ne z c with rfl | hz
  · refine (Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt ?_ ?_).differentiableAt
    · filter_upwards [self_mem_nhdsWithin] with w hw
      exact entireDividedDifference_differentiableAt_of_ne f hf (by simpa using hw)
    · simpa [entireDividedDifference] using (hf z).hasDerivAt.continuousAt_div
  · exact entireDividedDifference_differentiableAt_of_ne f hf hz

end BombieriVinogradov.SiegelWalfisz
