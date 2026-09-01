import Mathlib.NumberTheory.LSeries.DirichletContinuation
import PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.Gamma.StripBounds

/-!
# Growth of the completed Dirichlet Gamma factor

This module gives one absolute right-half-plane growth bound for the parity-dependent
Archimedean Gamma factor in a completed Dirichlet L-function.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem exists_norm_gammaFactor_le_exp_growth :
    exists C : Real, 0 < C ∧
      forall {N : Nat} (chi : DirichletCharacter Complex N) {s : Complex},
        (1 : Real) / 2 ≤ s.re -> 1 ≤ ‖s‖ ->
          ‖chi.gammaFactor s‖ ≤
            Real.exp (C * (2 + ‖s‖) * Real.log (2 + ‖s‖)) := by
  obtain ⟨C, hCPos, hC⟩ := Complex.Gammaℝ.Stirling.bound_re_ge_zero
  refine ⟨C, hCPos, ?_⟩
  intro N chi s hsRe hsNorm
  have hLogNonneg : 0 ≤ Real.log (2 + ‖s‖) :=
    Real.log_nonneg (by linarith [norm_nonneg s])
  rcases chi.even_or_odd with hEven | hOdd
  · rw [hEven.gammaFactor_def]
    have hGamma := hC s (by linarith) hsNorm
    apply hGamma.trans
    apply Real.exp_le_exp.mpr
    have hNormLe : ‖s‖ ≤ 2 + ‖s‖ := by linarith
    have hLogLe : Real.log (1 + ‖s‖) ≤ Real.log (2 + ‖s‖) := by
      apply Real.log_le_log
      · positivity
      · linarith
    have hLogSmallNonneg : 0 ≤ Real.log (1 + ‖s‖) :=
      Real.log_nonneg (by linarith [norm_nonneg s])
    have hFirst : C * ‖s‖ * Real.log (1 + ‖s‖) ≤
        C * (2 + ‖s‖) * Real.log (1 + ‖s‖) := by
      gcongr
    exact hFirst.trans (by gcongr)
  · rw [hOdd.gammaFactor_def]
    have hShiftRe : 0 ≤ (s + 1).re := by simp; linarith
    have hShiftNorm : 1 ≤ ‖s + 1‖ := by
      have hReLe : (s + 1).re ≤ ‖s + 1‖ :=
        le_trans (le_abs_self _) (Complex.abs_re_le_norm (s + 1))
      simp at hReLe
      linarith
    have hGamma := hC (s + 1) hShiftRe hShiftNorm
    apply hGamma.trans
    apply Real.exp_le_exp.mpr
    have hNormLe : ‖s + 1‖ ≤ 2 + ‖s‖ := by
      calc
        ‖s + 1‖ ≤ ‖s‖ + ‖(1 : Complex)‖ := norm_add_le _ _
        _ ≤ 2 + ‖s‖ := by simp; linarith
    have hOneNormLe : 1 + ‖s + 1‖ ≤ 2 + ‖s‖ := by
      have h := norm_add_le s (1 : Complex)
      simp only [norm_one] at h
      linarith
    have hLogLe : Real.log (1 + ‖s + 1‖) ≤ Real.log (2 + ‖s‖) := by
      apply Real.log_le_log
      · positivity
      · exact hOneNormLe
    have hLogSmallNonneg : 0 ≤ Real.log (1 + ‖s + 1‖) :=
      Real.log_nonneg (by linarith [norm_nonneg (s + 1)])
    have hFirst : C * ‖s + 1‖ * Real.log (1 + ‖s + 1‖) ≤
        C * (2 + ‖s‖) * Real.log (1 + ‖s + 1‖) := by
      gcongr
    exact hFirst.trans (by gcongr)

end BombieriVinogradov.SiegelWalfisz
