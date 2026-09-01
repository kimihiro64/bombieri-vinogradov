import BombieriVinogradov.Helpers.DirichletCharacter.CpowDerivativeMajorant

/-!
# Integrability of the Abel derivative majorant

This module owns integrability at infinity of the real power that majorizes the
derivative term in character Abel summation.
-/

set_option autoImplicit false

open Filter MeasureTheory

namespace BombieriVinogradov

/-- If `0 < re s`, then `t ^ (-(s + 1).re)` is integrable at infinity. -/
theorem integrableAtFilter_rpow_neg_add_one_re {s : ℂ} (hs : 0 < s.re) :
    IntegrableAtFilter (fun t : ℝ => t ^ (-(s + 1).re)) atTop := by
  refine integrableAtFilter_rpow_atTop_iff.mpr ?_
  simp only [Complex.add_re, Complex.one_re]
  linarith

end BombieriVinogradov
