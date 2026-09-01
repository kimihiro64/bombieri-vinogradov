import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Calculus of the Abel weight

This module owns differentiability and local derivative integrability of the
real-variable complex power `t ^ (-s)` on `[1, infinity)`.
-/

set_option autoImplicit false

open MeasureTheory Set

namespace BombieriVinogradov

/-- The Abel weight is differentiable at every real point at least one. -/
theorem differentiableAt_ofReal_cpow_neg {s : ℂ} (hs : 0 < s.re) {t : ℝ}
    (ht : t ∈ Ici 1) : DifferentiableAt ℝ (fun x : ℝ => (x : ℂ) ^ (-s)) t := by
  exact differentiableAt_id.ofReal_cpow_const (zero_lt_one.trans_le ht).ne'
    (neg_ne_zero.mpr (Complex.ne_zero_of_re_pos hs))

/-- The derivative of the Abel weight is locally integrable on `[1, infinity)`. -/
theorem locallyIntegrableOn_deriv_ofReal_cpow_neg {s : ℂ} (hs : 0 < s.re) :
    LocallyIntegrableOn (deriv (fun t : ℝ => (t : ℂ) ^ (-s))) (Ici 1) := by
  exact (Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi <|
    integrableOn_Ioi_deriv_ofReal_cpow zero_lt_one (by simpa using hs)).locallyIntegrableOn

end BombieriVinogradov
