import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Exceptional.ComplexDifferenceQuotient
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.Ring

/-!
# Reflected exceptional-zero cancellation

This module packages the exact cancellation between the reflected residue and
the reciprocal term supplied by the origin logarithmic derivative.
-/
set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

/-- The reciprocal term minus the reflected complex-power residue is bounded
by the quarter-power logarithmic scale. -/
theorem norm_reciprocal_sub_reflectedCpow_div_le
    {x : Real} (hx : 1 <= x) {beta : Complex}
    (hBetaIm : beta.im = 0) (hBetaLower : (3 / 4 : Real) <= beta.re)
    (hBetaUpper : beta.re < 1) :
    norm ((1 : Complex) / (1 - beta) -
        (x : Complex) ^ (1 - beta) / (1 - beta)) <=
      x ^ (1 / 4 : Real) * Real.log x := by
  have hIdentity :
      (1 : Complex) / (1 - beta) -
          (x : Complex) ^ (1 - beta) / (1 - beta) =
        -(((x : Complex) ^ (1 - beta) - 1) / (1 - beta)) := by
    ring
  rw [hIdentity, norm_neg]
  exact norm_reflectedCpowDifferenceQuotient_le
    hx hBetaIm hBetaLower hBetaUpper

end BombieriVinogradov.SiegelWalfisz
