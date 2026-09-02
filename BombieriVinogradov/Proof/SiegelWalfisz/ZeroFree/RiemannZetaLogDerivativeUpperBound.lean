import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.GammaFactorLogDerivativeScale
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.RiemannXiZeroSumPositivity
import Mathlib.Analysis.Real.Pi.Bounds
import PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.Gamma.DigammaSeries
import Robin1984.NicolasLandau.XiLogDerivative

/-!
# Riemann-zeta logarithmic derivative in the high strip

This module derives the source-form upper bound for the real part of
`-zeta'/zeta`, retaining the explicit pole term and absorbing every fixed or
gamma-factor contribution into one logarithmic height constant.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem exists_neg_re_logDeriv_riemannZeta_le_pole_add_log :
    exists C : Real, 0 < C ∧
      forall {s : Complex}, 1 < s.re -> s.re ≤ 2 ->
        (-deriv riemannZeta s / riemannZeta s).re ≤
          (1 / (s - 1)).re + C * Real.log (|s.im| + 2) := by
  obtain ⟨D, hDPos, hD⟩ :=
    Complex.exists_norm_digamma_le_log
      (a := (3 : Real) / 2) (b := 2) (by norm_num)
  let A : Real :=
    |(-logDeriv Complex.riemannXi 0).re| / Real.log 2
  let C : Real := A + D
  have hLogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hANonneg : 0 ≤ A := by
    dsimp [A]
    positivity
  have hCPos : 0 < C := by
    dsimp [C]
    linarith
  refine Exists.intro C (And.intro hCPos ?_)
  intro s hsLower hsUpper
  have hArgumentLower :
      (3 : Real) / 2 ≤ (s / 2 + 1).re := by
    rw [Complex.add_re, Complex.div_ofNat_re]
    norm_num
    linarith
  have hArgumentUpper : (s / 2 + 1).re ≤ 2 := by
    rw [Complex.add_re, Complex.div_ofNat_re]
    norm_num
    linarith
  have hArgumentIm : (s / 2 + 1).im = (s / 2).im := by
    simp
  have hDigamma :
      ‖Complex.digamma (s / 2 + 1)‖ ≤
        D * Real.log (|s.im| + 2) := by
    calc
      ‖Complex.digamma (s / 2 + 1)‖ ≤
          D * Real.log (|(s / 2 + 1).im| + 2) :=
        hD (s / 2 + 1) hArgumentLower hArgumentUpper
      _ = D * Real.log (|(s / 2).im| + 2) := by
        rw [hArgumentIm]
      _ ≤ D * Real.log (|s.im| + 2) :=
        mul_le_mul_of_nonneg_left
          (log_abs_im_div_two_add_two_le s) hDPos.le
  have hLogScaleLower :
      Real.log 2 ≤ Real.log (|s.im| + 2) := by
    apply Real.log_le_log (by norm_num)
    linarith [abs_nonneg s.im]
  have hConstantAbsorb :
      |(-logDeriv Complex.riemannXi 0).re| ≤
        A * Real.log (|s.im| + 2) := by
    calc
      |(-logDeriv Complex.riemannXi 0).re| =
          A * Real.log 2 := by
        dsimp [A]
        field_simp
      _ ≤ A * Real.log (|s.im| + 2) :=
        mul_le_mul_of_nonneg_left hLogScaleLower hANonneg
  have hXiConstant :
      -(logDeriv Complex.riemannXi 0).re ≤
        A * Real.log (|s.im| + 2) := by
    have hRaw :=
      (le_abs_self (-logDeriv Complex.riemannXi 0).re).trans
        hConstantAbsorb
    simpa only [Complex.neg_re] using hRaw
  have hZeroSum := riemannXi_logDerivTsum_re_nonneg hsLower
  have hHalfDigamma :
      ((1 / 2 : Complex) * Complex.digamma (s / 2 + 1)).re ≤
        D * Real.log (|s.im| + 2) := by
    calc
      ((1 / 2 : Complex) * Complex.digamma (s / 2 + 1)).re ≤
          ‖(1 / 2 : Complex) * Complex.digamma (s / 2 + 1)‖ :=
        Complex.re_le_norm _
      _ ≤ ‖Complex.digamma (s / 2 + 1)‖ := by
        rw [norm_mul]
        norm_num
        nlinarith [norm_nonneg (Complex.digamma (s / 2 + 1))]
      _ ≤ D * Real.log (|s.im| + 2) := hDigamma
  have hLogPi : 0 < Real.log Real.pi :=
    Real.log_pos ((by norm_num : (1 : Real) < 3).trans Real.pi_gt_three)
  have hPiTerm :
      0 ≤ ((1 / 2 : Complex) * Real.log Real.pi).re := by
    norm_num
    exact hLogPi.le
  have hFormula :=
    Robin1984.neg_riemannZeta_logDeriv_eq_xiDivisor_tsum hsLower
  rw [hFormula]
  simp only [Complex.add_re, Complex.sub_re, Complex.neg_re]
  dsimp [C]
  linarith

end BombieriVinogradov.SiegelWalfisz
