import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.NormalizationLogDerivative
import Mathlib.NumberTheory.LSeries.DirichletContinuation

/-!
# Logarithmic derivative of the symmetric completion at regular points

This module extends the exact three-factor logarithmic-derivative identity
beyond the positive half-plane whenever the ordinary and gamma factors are
regular and nonzero at the point.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem logDeriv_symmetricCompletedLFunction_eq_three_factors_of_regular
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : Ne chi 1) {s : Complex}
    (hLFunctionNe : Ne (chi.LFunction s) 0)
    (hGammaNe : Ne (chi.gammaFactor s) 0)
    (hGammaDifferentiable :
      DifferentiableAt Complex chi.gammaFactor s) :
    logDeriv (symmetricCompletedLFunction chi) s =
      (Real.log N : Complex) / 2 +
        (logDeriv chi.LFunction s + logDeriv chi.gammaFactor s) := by
  have hNNeOne : Ne N 1 := by
    intro hN
    exact hchi (chi.level_one' hN)
  have hCompletedValue :=
    chi.LFunction_eq_completed_div_gammaFactor s (Or.inr hNNeOne)
  have hCompletedNe : Ne (chi.completedLFunction s) 0 := by
    intro hCompletedZero
    apply hLFunctionNe
    rw [hCompletedValue, hCompletedZero]
    simp
  have hLFunctionDifferentiable :
      DifferentiableAt Complex chi.LFunction s :=
    DirichletCharacter.differentiableAt_LFunction chi s (Or.inr hchi)
  have hCompletedDifferentiable :
      DifferentiableAt Complex chi.completedLFunction s :=
    (chi.differentiable_completedLFunction hchi).differentiableAt
  have hLFunctionAsQuotient :
      chi.LFunction = fun z : Complex =>
        chi.completedLFunction z / chi.gammaFactor z := by
    funext z
    exact chi.LFunction_eq_completed_div_gammaFactor z (Or.inr hNNeOne)
  have hLFunctionLogDerivative :
      logDeriv chi.LFunction s =
        logDeriv chi.completedLFunction s -
          logDeriv chi.gammaFactor s := by
    rw [hLFunctionAsQuotient]
    exact logDeriv_div s hCompletedNe hGammaNe
      hCompletedDifferentiable hGammaDifferentiable
  have hNCast : Ne (N : Complex) 0 := by
    norm_num [NeZero.ne N]
  have hNormalizationNe :
      Ne ((N : Complex) ^ (s / 2)) 0 := by
    simp [hNCast]
  have hNormalizationDifferentiable :
      DifferentiableAt Complex
        (fun z : Complex => (N : Complex) ^ (z / 2)) s :=
    ((differentiable_id.div_const (2 : Complex)).const_cpow
      (.inl hNCast)).differentiableAt
  have hOuter :=
    logDeriv_mul s hNormalizationNe hCompletedNe
      hNormalizationDifferentiable hCompletedDifferentiable
  calc
    logDeriv (symmetricCompletedLFunction chi) s =
        logDeriv (fun z : Complex => (N : Complex) ^ (z / 2)) s +
          logDeriv chi.completedLFunction s := by
      exact hOuter
    _ = (Real.log N : Complex) / 2 +
        logDeriv chi.completedLFunction s := by
      rw [logDeriv_symmetricNormalization]
    _ = (Real.log N : Complex) / 2 +
        (logDeriv chi.LFunction s + logDeriv chi.gammaFactor s) := by
      rw [hLFunctionLogDerivative]
      ring

end BombieriVinogradov.SiegelWalfisz
