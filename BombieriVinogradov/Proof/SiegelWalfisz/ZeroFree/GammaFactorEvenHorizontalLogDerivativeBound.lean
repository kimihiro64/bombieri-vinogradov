import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.GammaFactorLeftLineLogDerivative
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.GammaFactorLogDerivativeBoundCore
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.GammaFactorLogDerivativeScale
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.Gamma.DigammaSeries

/-!
# Even-character gamma bound on the horizontal contour strip

This module proves only the even-character logarithmic-derivative estimate
needed on the bounded horizontal strip. Odd characters and the parity
combination belong to separate modules.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem exists_norm_logDeriv_gammaFactor_le_log_of_even_horizontal_strip :
    exists C : Real, And (0 < C)
      (forall {N : Nat} {chi : DirichletCharacter Complex N},
        DirichletCharacter.Even chi ->
          forall {s : Complex},
            -(1 : Real) / 2 <= s.re ->
            s.re <= 2 ->
            2 <= abs s.im ->
              norm (logDeriv chi.gammaFactor s) <=
                C * Real.log (abs s.im + 2)) := by
  choose D hDPos hD using
    Complex.exists_norm_digamma_le_log
      (a := (3 : Real) / 4) (b := 2) (by norm_num)
  have hLogFourPos : 0 < Real.log 4 :=
    Real.log_pos (by norm_num)
  let E : Real := D + 1 / Real.log 4
  have hEPos : 0 < E := by
    dsimp [E]
    positivity
  let C : Real := Real.log Real.pi / Real.log 2 + E
  have hLogPi : 0 < Real.log Real.pi :=
    Real.log_pos ((by norm_num : (1 : Real) < 3).trans Real.pi_gt_three)
  have hLogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hCPos : 0 < C := by
    dsimp [C]
    positivity
  refine Exists.intro C (And.intro hCPos ?_)
  intro N chi hEven s hsLower hsUpper hsIm
  have hsNegOne : -1 < s.re := by
    linarith
  have hs0 : Ne s 0 := by
    intro hsZero
    rw [hsZero] at hsIm
    norm_num at hsIm
  have hFormula :
      logDeriv chi.gammaFactor s =
        -(Real.log Real.pi : Complex) / 2 +
          (1 / 2 : Complex) * Complex.digamma (s / 2) :=
    logDeriv_gammaFactor_of_even_of_neg_one_lt_re_of_ne_zero
      hEven hsNegOne hs0
  have hRecurrence :=
    Complex.digamma_apply_add_one (s / 2)
      (half_ne_neg_nat_of_neg_one_lt_re_of_ne_zero hsNegOne hs0)
  have hShift : s / 2 + 1 = (s + 2) / 2 := by
    ring
  rw [hShift] at hRecurrence
  have hDigammaIdentity :
      Complex.digamma (s / 2) =
        Complex.digamma ((s + 2) / 2) - Inv.inv (s / 2) := by
    rw [hRecurrence]
    ring
  have hShiftLower :
      (3 : Real) / 4 <= ((s + 2) / 2).re := by
    rw [Complex.div_ofNat_re, Complex.add_re]
    norm_num
    linarith
  have hShiftUpper :
      ((s + 2) / 2).re <= 2 := by
    rw [Complex.div_ofNat_re, Complex.add_re]
    norm_num
    linarith
  have hShiftedDigamma :
      norm (Complex.digamma ((s + 2) / 2)) <=
        D * Real.log (abs ((s + 2) / 2).im + 2) :=
    hD ((s + 2) / 2) hShiftLower hShiftUpper
  have hShiftIm : ((s + 2) / 2).im = (s / 2).im := by
    simp
  have hScale :
      Real.log (abs ((s + 2) / 2).im + 2) <=
        Real.log (abs s.im + 2) := by
    rw [hShiftIm]
    exact log_abs_im_div_two_add_two_le s
  have hShiftedDigammaLog :
      norm (Complex.digamma ((s + 2) / 2)) <=
        D * Real.log (abs s.im + 2) :=
    hShiftedDigamma.trans
      (mul_le_mul_of_nonneg_left hScale hDPos.le)
  have hHalfIm : abs (s / 2).im = abs s.im / 2 := by
    rw [Complex.div_ofNat_im, abs_div]
    norm_num
  have hHalfImLower : 1 <= abs (s / 2).im := by
    rw [hHalfIm]
    linarith
  have hHalfNormLower : 1 <= norm (s / 2) :=
    hHalfImLower.trans (Complex.abs_im_le_norm (s / 2))
  have hInv : norm (Inv.inv (s / 2)) <= (1 : Real) := by
    calc
      norm (Inv.inv (s / 2)) = Inv.inv (norm (s / 2)) := by
        rw [norm_inv]
      _ = 1 / norm (s / 2) := by rw [one_div]
      _ <= 1 / (1 : Real) :=
        one_div_le_one_div_of_le (by norm_num) hHalfNormLower
      _ = 1 := by norm_num
  have hLogFourLower :
      Real.log 4 <= Real.log (abs s.im + 2) :=
    Real.log_le_log (by norm_num) (by linarith)
  have hOneAbsorb :
      (1 : Real) <=
        (1 / Real.log 4) * Real.log (abs s.im + 2) := by
    calc
      (1 : Real) = (1 / Real.log 4) * Real.log 4 := by
        field_simp
      _ <= (1 / Real.log 4) * Real.log (abs s.im + 2) :=
        mul_le_mul_of_nonneg_left hLogFourLower
          (div_nonneg (by norm_num) hLogFourPos.le)
  have hDigammaLog :
      norm (Complex.digamma (s / 2)) <=
        E * Real.log (abs s.im + 2) := by
    rw [hDigammaIdentity]
    calc
      norm (Complex.digamma ((s + 2) / 2) - Inv.inv (s / 2)) <=
          norm (Complex.digamma ((s + 2) / 2)) +
            norm (Inv.inv (s / 2)) :=
        norm_sub_le _ _
      _ <= D * Real.log (abs s.im + 2) + 1 :=
        add_le_add hShiftedDigammaLog hInv
      _ <= D * Real.log (abs s.im + 2) +
          (1 / Real.log 4) * Real.log (abs s.im + 2) :=
        add_le_add le_rfl hOneAbsorb
      _ = E * Real.log (abs s.im + 2) := by
        dsimp [E]
        ring
  have hCore :=
    norm_logDeriv_gammaFactor_le_log_of_formula hEPos hFormula hDigammaLog
  simpa [C] using hCore.2

end BombieriVinogradov.SiegelWalfisz

