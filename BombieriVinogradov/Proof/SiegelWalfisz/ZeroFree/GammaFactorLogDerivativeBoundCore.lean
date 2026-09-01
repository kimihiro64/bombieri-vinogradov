import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.GammaFactorLogDerivative
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Constant absorption for gamma-factor logarithmic derivative bounds

This module turns a vertical-strip digamma estimate into the corresponding gamma-factor
logarithmic-derivative estimate, including one uniform absorption of the `log pi` term.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem norm_logDeriv_gammaFactor_le_log_of_formula
    {N : Nat} {chi : DirichletCharacter Complex N} {s z : Complex}
    {D : Real} (hDPos : 0 < D)
    (hFormula :
      logDeriv chi.gammaFactor s =
        -(Real.log Real.pi : Complex) / 2 +
          (1 / 2 : Complex) * Complex.digamma z)
    (hDigamma :
      ‖Complex.digamma z‖ ≤ D * Real.log (|s.im| + 2)) :
    0 < Real.log Real.pi / Real.log 2 + D ∧
      ‖logDeriv chi.gammaFactor s‖ ≤
        (Real.log Real.pi / Real.log 2 + D) *
          Real.log (|s.im| + 2) := by
  have hLogPi : 0 < Real.log Real.pi :=
    Real.log_pos ((by norm_num : (1 : Real) < 3).trans Real.pi_gt_three)
  have hLogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  apply And.intro
  · positivity
  · have hLogTwoLe : Real.log 2 ≤ Real.log (|s.im| + 2) := by
      apply Real.log_le_log (by norm_num)
      linarith [abs_nonneg s.im]
    have hPiAbsorb :
        Real.log Real.pi ≤
          (Real.log Real.pi / Real.log 2) * Real.log (|s.im| + 2) := by
      calc
        Real.log Real.pi =
            (Real.log Real.pi / Real.log 2) * Real.log 2 := by
          field_simp
        _ ≤ (Real.log Real.pi / Real.log 2) *
            Real.log (|s.im| + 2) := by
          exact mul_le_mul_of_nonneg_left hLogTwoLe
            (div_nonneg hLogPi.le hLogTwo.le)
    have hPiTerm :
        ‖-(Real.log Real.pi : Complex) / 2‖ ≤ Real.log Real.pi := by
      simp [abs_of_pos hLogPi]
      linarith
    have hHalfTerm :
        ‖(1 / 2 : Complex) * Complex.digamma z‖ ≤
          ‖Complex.digamma z‖ := by
      rw [norm_mul]
      norm_num
      nlinarith [norm_nonneg (Complex.digamma z)]
    rw [hFormula]
    calc
      ‖-(Real.log Real.pi : Complex) / 2 +
          (1 / 2 : Complex) * Complex.digamma z‖ ≤
          ‖-(Real.log Real.pi : Complex) / 2‖ +
            ‖(1 / 2 : Complex) * Complex.digamma z‖ :=
        norm_add_le _ _
      _ ≤ Real.log Real.pi + ‖Complex.digamma z‖ :=
        add_le_add hPiTerm hHalfTerm
      _ ≤ Real.log Real.pi + D * Real.log (|s.im| + 2) :=
        add_le_add le_rfl hDigamma
      _ ≤ (Real.log Real.pi / Real.log 2) *
          Real.log (|s.im| + 2) + D * Real.log (|s.im| + 2) :=
        add_le_add hPiAbsorb le_rfl
      _ = (Real.log Real.pi / Real.log 2 + D) *
          Real.log (|s.im| + 2) := by ring

end BombieriVinogradov.SiegelWalfisz
