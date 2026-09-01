import BombieriVinogradov.Helpers.DirichletCharacter.LFunctionHalfPlaneBound
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedGammaFactorGrowth
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedNormalization
import PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Right-half-plane growth of the symmetric completed L-function

This module combines the character L-function, modulus-power, and Archimedean-factor
estimates into an order-one exponential bound on `re s >= 1 / 2`.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem symmetricCompletedLFunction_rightHalfPlane_order_bound
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N) (hchi : chi ≠ 1) :
    forall epsilon : Real, 0 < epsilon ->
      exists C : Real, 0 < C ∧ forall s : Complex,
        (1 : Real) / 2 ≤ s.re -> 1 ≤ ‖s‖ ->
          ‖symmetricCompletedLFunction chi s‖ ≤
            Real.exp (C * (2 + ‖s‖) ^ (1 + epsilon)) := by
  intro epsilon hEpsilon
  obtain ⟨Cgamma, hCgammaPos, hGamma⟩ := exists_norm_gammaFactor_le_exp_growth
  have hNPosNat : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hNPos : 0 < (N : Real) := by exact_mod_cast hNPosNat
  have hNOne : 1 ≤ (N : Real) := by exact_mod_cast hNPosNat
  have hLogNNonneg : 0 ≤ Real.log (N : Real) := Real.log_nonneg hNOne
  let C : Real := Real.log (N : Real) + 2 * (N : Real) + Cgamma / epsilon + 1
  have hCPos : 0 < C := by
    dsimp [C]
    have hRatioPos : 0 < Cgamma / epsilon := div_pos hCgammaPos hEpsilon
    positivity
  refine ⟨C, hCPos, ?_⟩
  intro s hsRe hsNorm
  let R : Real := 2 + ‖s‖
  have hRPos : 0 < R := by dsimp [R]; positivity
  have hROne : 1 ≤ R := by dsimp [R]; linarith [norm_nonneg s]
  have hExponentNonneg : 0 ≤ (1 + epsilon : Real) := by linarith
  have hRLePow : R ≤ R ^ (1 + epsilon) := by
    have hPower := Real.rpow_le_rpow_of_exponent_le hROne
      (show (1 : Real) ≤ 1 + epsilon by linarith)
    simpa [Real.rpow_one] using hPower
  have hCpow : ‖(N : Complex) ^ (s / 2)‖ ≤
      Real.exp (Real.log (N : Real) * R) := by
    change ‖((N : Real) : Complex) ^ (s / 2)‖ ≤
      Real.exp (Real.log (N : Real) * R)
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hNPos,
      Real.rpow_def_of_pos hNPos]
    apply Real.exp_le_exp.mpr
    apply mul_le_mul_of_nonneg_left _ hLogNNonneg
    have hReLeNorm : s.re ≤ ‖s‖ :=
      le_trans (le_abs_self _) (Complex.abs_re_le_norm s)
    have hHalfRe : (s / 2).re = s.re / 2 := by simp
    rw [hHalfRe]
    dsimp [R]
    linarith
  have hLFunction : ‖chi.LFunction s‖ ≤
      Real.exp ((2 * (N : Real)) * R) := by
    have hL := BombieriVinogradov.norm_LFunction_le_two_mul_modulus_mul_norm
      chi hchi hsRe
    apply hL.trans
    have hLinear : 2 * (N : Real) * ‖s‖ ≤ 2 * (N : Real) * R := by
      gcongr
      dsimp [R]
      linarith
    exact hLinear.trans (Real.le_exp_self _)
  have hGammaFactor : ‖chi.gammaFactor s‖ ≤
      Real.exp (Cgamma * R * Real.log R) := by
    simpa [R] using hGamma chi hsRe hsNorm
  have hGammaFactorNe : chi.gammaFactor s ≠ 0 := by
    rcases chi.even_or_odd with hEven | hOdd
    · rw [hEven.gammaFactor_def]
      exact Complex.Gammaℝ_ne_zero_of_re_pos (by linarith)
    · rw [hOdd.gammaFactor_def]
      exact Complex.Gammaℝ_ne_zero_of_re_pos (by simp; linarith)
  have hCompleted : chi.completedLFunction s =
      chi.LFunction s * chi.gammaFactor s := by
    have hNNeOne : N ≠ 1 := by
      intro hN
      exact hchi (chi.level_one' hN)
    exact ((eq_div_iff hGammaFactorNe).mp
      (chi.LFunction_eq_completed_div_gammaFactor s (.inr hNNeOne))).symm
  have hRaw : ‖symmetricCompletedLFunction chi s‖ ≤
      Real.exp (Real.log (N : Real) * R) *
        (Real.exp ((2 * (N : Real)) * R) *
          Real.exp (Cgamma * R * Real.log R)) := by
    rw [symmetricCompletedLFunction, hCompleted, norm_mul, norm_mul]
    exact mul_le_mul hCpow
      (mul_le_mul hLFunction hGammaFactor (norm_nonneg _) (Real.exp_pos _).le)
      (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      (Real.exp_pos _).le
  have hRawExp : ‖symmetricCompletedLFunction chi s‖ ≤
      Real.exp ((Real.log (N : Real) + 2 * (N : Real)) * R +
        Cgamma * R * Real.log R) := by
    apply hRaw.trans_eq
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have hLog : Real.log R ≤ R ^ epsilon / epsilon :=
    Real.log_le_rpow_div hRPos.le hEpsilon
  have hRLog : R * Real.log R ≤ (1 / epsilon) * R ^ (1 + epsilon) := by
    have hStep := mul_le_mul_of_nonneg_left hLog hRPos.le
    calc
      R * Real.log R ≤ R * (R ^ epsilon / epsilon) := hStep
      _ = (1 / epsilon) * R ^ (1 + epsilon) := by
        rw [Real.rpow_add hRPos]
        simp [Real.rpow_one]
        field_simp [hEpsilon.ne']
  have hMainExponent :
      (Real.log (N : Real) + 2 * (N : Real)) * R +
          Cgamma * R * Real.log R ≤
        C * R ^ (1 + epsilon) := by
    have hLinearCoeff : 0 ≤ Real.log (N : Real) + 2 * (N : Real) := by positivity
    have hLinear : (Real.log (N : Real) + 2 * (N : Real)) * R ≤
        (Real.log (N : Real) + 2 * (N : Real)) * R ^ (1 + epsilon) :=
      mul_le_mul_of_nonneg_left hRLePow hLinearCoeff
    have hGammaPower : Cgamma * (R * Real.log R) ≤
        (Cgamma / epsilon) * R ^ (1 + epsilon) := by
      have hStep := mul_le_mul_of_nonneg_left hRLog hCgammaPos.le
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hStep
    calc
      (Real.log (N : Real) + 2 * (N : Real)) * R +
          Cgamma * R * Real.log R ≤
        (Real.log (N : Real) + 2 * (N : Real)) * R ^ (1 + epsilon) +
          (Cgamma / epsilon) * R ^ (1 + epsilon) := by
            exact add_le_add hLinear (by simpa [mul_assoc] using hGammaPower)
      _ = (Real.log (N : Real) + 2 * (N : Real) + Cgamma / epsilon) *
          R ^ (1 + epsilon) := by ring
      _ ≤ C * R ^ (1 + epsilon) := by
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hRPos.le _)
        dsimp [C]
        linarith
  exact hRawExp.trans (Real.exp_le_exp.mpr hMainExponent)

end BombieriVinogradov.SiegelWalfisz
