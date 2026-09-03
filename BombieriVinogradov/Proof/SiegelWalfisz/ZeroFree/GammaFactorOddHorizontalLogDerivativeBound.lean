import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.GammaFactorLeftLineLogDerivative
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.GammaFactorLogDerivativeBoundCore
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.GammaFactorLogDerivativeScale
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.Gamma.DigammaSeries

/-!
# Odd-character gamma bound on the horizontal contour strip

This module proves only the odd-character logarithmic-derivative estimate
needed on the bounded horizontal strip. Even characters and the parity
combination belong to separate modules.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem exists_norm_logDeriv_gammaFactor_le_log_of_odd_horizontal_strip :
    exists C : Real, And (0 < C)
      (forall {N : Nat} {chi : DirichletCharacter Complex N},
        DirichletCharacter.Odd chi ->
          forall {s : Complex},
            -(1 : Real) / 2 <= s.re ->
            s.re <= 2 ->
            2 <= abs s.im ->
              norm (logDeriv chi.gammaFactor s) <=
                C * Real.log (abs s.im + 2)) := by
  choose D hDPos hD using
    Complex.exists_norm_digamma_le_log
      (a := (1 : Real) / 4) (b := (3 : Real) / 2) (by norm_num)
  let C : Real := Real.log Real.pi / Real.log 2 + D
  have hLogPi : 0 < Real.log Real.pi :=
    Real.log_pos ((by norm_num : (1 : Real) < 3).trans Real.pi_gt_three)
  have hLogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hCPos : 0 < C := by
    dsimp [C]
    positivity
  refine Exists.intro C (And.intro hCPos ?_)
  intro N chi hOdd s hsLower hsUpper _hsIm
  have hsNegOne : -1 < s.re := by
    linarith
  have hArgumentLower :
      (1 : Real) / 4 <= ((s + 1) / 2).re := by
    rw [Complex.div_ofNat_re, Complex.add_re]
    norm_num
    linarith
  have hArgumentUpper :
      ((s + 1) / 2).re <= (3 : Real) / 2 := by
    rw [Complex.div_ofNat_re, Complex.add_re]
    norm_num
    linarith
  have hDigamma :
      norm (Complex.digamma ((s + 1) / 2)) <=
        D * Real.log (abs ((s + 1) / 2).im + 2) :=
    hD ((s + 1) / 2) hArgumentLower hArgumentUpper
  have hDigammaLog :
      norm (Complex.digamma ((s + 1) / 2)) <=
        D * Real.log (abs s.im + 2) :=
    hDigamma.trans
      (mul_le_mul_of_nonneg_left
        (log_abs_im_add_one_div_two_add_two_le s) hDPos.le)
  have hFormula :
      logDeriv chi.gammaFactor s =
        -(Real.log Real.pi : Complex) / 2 +
          (1 / 2 : Complex) * Complex.digamma ((s + 1) / 2) :=
    logDeriv_gammaFactor_of_odd_of_neg_one_lt_re hOdd hsNegOne
  have hCore :=
    norm_logDeriv_gammaFactor_le_log_of_formula hDPos hFormula hDigammaLog
  simpa [C] using hCore.2

end BombieriVinogradov.SiegelWalfisz

