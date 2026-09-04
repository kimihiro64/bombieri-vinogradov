import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

/-!
# Comparing a two-term complex sum with a reference sum

The two discrepancies are kept separate so their independently proved
bounds can be combined without changing the reference residual.
-/
set_option autoImplicit false

namespace BombieriVinogradov.ComplexAnalysis

theorem norm_sum_le_reference_and_differences (a b u v : Complex) :
    norm (a + b) <= norm (u + v) + norm (a - u) + norm (b - v) := by
  have hIdentity : a + b = (u + v) + (a - u) + (b - v) := by ring
  rw [hIdentity]
  exact norm_add_le_of_le (norm_add_le _ _) (le_refl (norm (b - v)))

end BombieriVinogradov.ComplexAnalysis
