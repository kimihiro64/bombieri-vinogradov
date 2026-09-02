import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.DigammaNegativeQuarterBound
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.GammaFactorLeftLineLogDerivative
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.GammaFactorLogDerivativeBoundCore

/-!
# Even gamma-factor bound on the explicit-formula left line

This module combines the negative-quarter digamma estimate with the exact
even-character logarithmic derivative formula.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem exists_norm_logDeriv_gammaFactor_left_line_le_log_of_even :
    exists C : Real, And (0 < C)
      (forall {N : Nat} {chi : DirichletCharacter Complex N},
        DirichletCharacter.Even chi ->
          forall {s : Complex}, s.re = -(1 : Real) / 2 ->
            norm (logDeriv chi.gammaFactor s) <=
              C * Real.log (abs s.im + 2)) := by
  choose D hDPos hD using
    exists_norm_digamma_half_le_log_of_re_eq_neg_one_half
  let C : Real := Real.log Real.pi / Real.log 2 + D
  have hLogPi : 0 < Real.log Real.pi :=
    Real.log_pos ((by norm_num : (1 : Real) < 3).trans Real.pi_gt_three)
  have hLogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hCPos : 0 < C := by
    dsimp [C]
    positivity
  refine Exists.intro C (And.intro hCPos ?_)
  intro N chi hEven s hsRe
  have hsRange : -1 < s.re := by
    rw [hsRe]
    norm_num
  have hs0 : Ne s 0 := by
    intro hsZero
    rw [hsZero] at hsRe
    norm_num at hsRe
  have hCore :=
    norm_logDeriv_gammaFactor_le_log_of_formula hDPos
      (logDeriv_gammaFactor_of_even_of_neg_one_lt_re_of_ne_zero
        hEven hsRange hs0)
      (hD hsRe)
  exact hCore.2

end BombieriVinogradov.SiegelWalfisz
