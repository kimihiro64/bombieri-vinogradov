import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Exceptional.RealDifferenceQuotient
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Complex reflected-zero difference quotient

This module lifts the real difference-quotient estimate to the complex cpow
expression contributed by a real reflected exceptional zero.
-/
set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

/-- A real reflected-zero quotient with exponent at most one quarter has norm
bounded by the quarter-power logarithmic scale. -/
theorem norm_reflectedCpowDifferenceQuotient_le
    {x : Real} (hx : 1 <= x) {beta : Complex}
    (hBetaIm : beta.im = 0) (hBetaLower : (3 / 4 : Real) <= beta.re)
    (hBetaUpper : beta.re < 1) :
    norm (((x : Complex) ^ (1 - beta) - 1) / (1 - beta)) <=
      x ^ (1 / 4 : Real) * Real.log x := by
  have hDeltaPos : 0 < 1 - beta.re := sub_pos.mpr hBetaUpper
  have hDeltaUpper : 1 - beta.re <= (1 / 4 : Real) := by
    linarith
  have hExponent : 1 - beta = ((1 - beta.re : Real) : Complex) := by
    apply Complex.ext <;> simp [hBetaIm]
  have hQuotient :
      ((x : Complex) ^ (1 - beta) - 1) / (1 - beta) =
        (((x ^ (1 - beta.re) - 1) / (1 - beta.re) : Real) : Complex) := by
    rw [hExponent]
    rw [Eq.symm (Complex.ofReal_cpow (zero_le_one.trans hx) (1 - beta.re))]
    norm_num
  have hOneLe : 1 <= x ^ (1 - beta.re) :=
    Real.one_le_rpow hx hDeltaPos.le
  rw [hQuotient, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg (sub_nonneg.mpr hOneLe) hDeltaPos.le)]
  exact rpow_sub_one_div_le_quarterPower_mul_log hx hDeltaPos hDeltaUpper

end BombieriVinogradov.SiegelWalfisz
