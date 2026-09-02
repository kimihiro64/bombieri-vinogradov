import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.GammaFactorLogDerivativeScale
import PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.Gamma.DigammaSeries

/-!
# Digamma bound on the positive quarter line

This module applies the right-half-plane digamma estimate at real part one
quarter and compares the resulting vertical scale with the contour parameter.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem exists_norm_digamma_add_one_half_le_log_of_re_eq_neg_one_half :
    exists C : Real, And (0 < C)
      (forall {s : Complex}, s.re = -(1 : Real) / 2 ->
        norm (Complex.digamma ((s + 1) / 2)) <=
          C * Real.log (abs s.im + 2)) := by
  choose C hCPos hC using
    Complex.exists_norm_digamma_le_log
      (a := (1 : Real) / 4) (b := (1 : Real) / 4) (by norm_num)
  refine Exists.intro C (And.intro hCPos ?_)
  intro s hsRe
  have hArgumentRe : ((s + 1) / 2).re = (1 : Real) / 4 := by
    rw [Complex.div_ofNat_re, Complex.add_re, hsRe]
    norm_num
  have hDigamma :=
    hC ((s + 1) / 2) (by rw [hArgumentRe]) (by rw [hArgumentRe])
  exact hDigamma.trans
    (mul_le_mul_of_nonneg_left
      (log_abs_im_add_one_div_two_add_two_le s) hCPos.le)

end BombieriVinogradov.SiegelWalfisz
