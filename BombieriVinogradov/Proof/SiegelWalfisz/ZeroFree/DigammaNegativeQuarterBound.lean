import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.GammaFactorLogDerivativeScale
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.GammaHalfNearOriginRegularity
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.Gamma.DigammaSeries

/-!
# Digamma bound on the negative quarter line

This module shifts the digamma argument from real part minus one quarter to
real part three quarters and absorbs the recurrence term uniformly.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem exists_norm_digamma_half_le_log_of_re_eq_neg_one_half :
    exists C : Real, And (0 < C)
      (forall {s : Complex}, s.re = -(1 : Real) / 2 ->
        norm (Complex.digamma (s / 2)) <=
          C * Real.log (abs s.im + 2)) := by
  choose D hDPos hD using
    Complex.exists_norm_digamma_le_log
      (a := (3 : Real) / 4) (b := (3 : Real) / 4) (by norm_num)
  have hLogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let C : Real := D + 4 / Real.log 2
  have hCPos : 0 < C := by
    dsimp [C]
    positivity
  refine Exists.intro C (And.intro hCPos ?_)
  intro s hsRe
  have hsRange : -1 < s.re := by
    rw [hsRe]
    norm_num
  have hs0 : Ne s 0 := by
    intro hsZero
    rw [hsZero] at hsRe
    norm_num at hsRe
  have hRecurrence :=
    Complex.digamma_apply_add_one (s / 2)
      (half_ne_neg_nat_of_neg_one_lt_re_of_ne_zero hsRange hs0)
  have hShift : s / 2 + 1 = (s + 2) / 2 := by ring
  rw [hShift] at hRecurrence
  have hIdentity :
      Complex.digamma (s / 2) =
        Complex.digamma ((s + 2) / 2) - Inv.inv (s / 2) := by
    rw [hRecurrence]
    ring
  have hShiftRe : ((s + 2) / 2).re = (3 : Real) / 4 := by
    rw [Complex.div_ofNat_re, Complex.add_re, hsRe]
    norm_num
  have hShiftedDigamma :=
    hD ((s + 2) / 2) (by rw [hShiftRe]) (by rw [hShiftRe])
  have hScale :
      Real.log (abs ((s + 2) / 2).im + 2) <=
        Real.log (abs s.im + 2) := by
    simpa using log_abs_im_div_two_add_two_le s
  have hShiftedDigammaLog :
      norm (Complex.digamma ((s + 2) / 2)) <=
        D * Real.log (abs s.im + 2) :=
    hShiftedDigamma.trans
      (mul_le_mul_of_nonneg_left hScale hDPos.le)
  have hHalfRe : (s / 2).re = -(1 : Real) / 4 := by
    rw [Complex.div_ofNat_re, hsRe]
    norm_num
  have hNormLower : (1 : Real) / 4 <= norm (s / 2) := by
    calc
      (1 : Real) / 4 = abs (s / 2).re := by
        rw [hHalfRe]
        norm_num
      _ <= norm (s / 2) := Complex.abs_re_le_norm _
  have hInv : norm (Inv.inv (s / 2)) <= (4 : Real) := by
    rw [norm_inv]
    have hReciprocal :
        1 / norm (s / 2) <= 1 / ((1 : Real) / 4) :=
      one_div_le_one_div_of_le (by norm_num) hNormLower
    have hQuarter : 1 / ((1 : Real) / 4) = 4 := by norm_num
    rw [hQuarter] at hReciprocal
    simpa only [one_div] using hReciprocal
  have hLogLower : Real.log 2 <= Real.log (abs s.im + 2) :=
    Real.log_le_log (by norm_num) (by linarith [abs_nonneg s.im])
  have hFourAbsorb :
      (4 : Real) <=
        (4 / Real.log 2) * Real.log (abs s.im + 2) := by
    calc
      (4 : Real) = (4 / Real.log 2) * Real.log 2 := by
        field_simp
      _ <= (4 / Real.log 2) * Real.log (abs s.im + 2) :=
        mul_le_mul_of_nonneg_left hLogLower
          (div_nonneg (by norm_num) hLogTwo.le)
  rw [hIdentity]
  calc
    norm (Complex.digamma ((s + 2) / 2) - Inv.inv (s / 2)) <=
        norm (Complex.digamma ((s + 2) / 2)) + norm (Inv.inv (s / 2)) :=
      norm_sub_le _ _
    _ <= D * Real.log (abs s.im + 2) + 4 :=
      add_le_add hShiftedDigammaLog hInv
    _ <= D * Real.log (abs s.im + 2) +
        (4 / Real.log 2) * Real.log (abs s.im + 2) :=
      add_le_add le_rfl hFourAbsorb
    _ = C * Real.log (abs s.im + 2) := by
      dsimp [C]
      ring

end BombieriVinogradov.SiegelWalfisz
