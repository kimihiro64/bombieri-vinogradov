import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedProductFormula
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.GammaFactorRegularity
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.NormalizationLogDerivative
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
# Logarithmic derivative of the symmetric completion

This module splits the logarithmic derivative of the symmetric completed Dirichlet
L-function into its modulus normalization, ordinary L-function, and gamma-factor terms.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem logDeriv_symmetricCompletedLFunction_eq_three_factors
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : chi ≠ 1) {s : Complex} (hs : 1 < s.re) :
    logDeriv (symmetricCompletedLFunction chi) s =
      (Real.log N : Complex) / 2 +
        (logDeriv chi.LFunction s + logDeriv chi.gammaFactor s) := by
  have hPositive : 0 < s.re := lt_trans zero_lt_one hs
  have hHalfPlane : {z : Complex | 0 < z.re} ∈ nhds s :=
    (Complex.continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds hPositive
  have hEventually :
      symmetricCompletedLFunction chi =ᶠ[nhds s]
        fun z : Complex =>
          (N : Complex) ^ (z / 2) *
            (chi.LFunction z * chi.gammaFactor z) := by
    filter_upwards [hHalfPlane] with z hz
    rw [symmetricCompletedLFunction,
      DirichletCharacter.completedLFunction_eq_LFunction_mul_gammaFactor_of_re_pos
        chi hz]
  have hCongruent :
      logDeriv (symmetricCompletedLFunction chi) s =
        logDeriv
          (fun z : Complex =>
            (N : Complex) ^ (z / 2) *
              (chi.LFunction z * chi.gammaFactor z)) s :=
    (logDeriv_congr_nhds hEventually).self_of_nhds
  have hN : (N : Complex) ≠ 0 := by
    exact_mod_cast NeZero.ne N
  have hNormalizationNe : (N : Complex) ^ (s / 2) ≠ 0 := by
    simp [hN]
  have hNormalizationDifferentiable :
      DifferentiableAt Complex (fun z : Complex => (N : Complex) ^ (z / 2)) s :=
    ((differentiable_id.div_const (2 : Complex)).const_cpow (.inl hN)).differentiableAt
  have hLFunctionNe : chi.LFunction s ≠ 0 :=
    DirichletCharacter.LFunction_ne_zero_of_one_le_re
      chi (.inl hchi) hs.le
  have hLFunctionDifferentiable :
      DifferentiableAt Complex chi.LFunction s :=
    DirichletCharacter.differentiableAt_LFunction chi s (.inr hchi)
  have hGammaNe : chi.gammaFactor s ≠ 0 :=
    DirichletCharacter.gammaFactor_ne_zero_of_re_pos chi hPositive
  have hGammaDifferentiable : DifferentiableAt Complex chi.gammaFactor s :=
    DirichletCharacter.differentiableAt_gammaFactor_of_re_pos chi hPositive
  have hProductNe : chi.LFunction s * chi.gammaFactor s ≠ 0 :=
    mul_ne_zero hLFunctionNe hGammaNe
  have hOuter :=
    logDeriv_mul s hNormalizationNe hProductNe
      hNormalizationDifferentiable
      (hLFunctionDifferentiable.mul hGammaDifferentiable)
  have hInner :=
    logDeriv_mul s hLFunctionNe hGammaNe
      hLFunctionDifferentiable hGammaDifferentiable
  calc
    logDeriv (symmetricCompletedLFunction chi) s =
        logDeriv
          (fun z : Complex =>
            (N : Complex) ^ (z / 2) *
              (chi.LFunction z * chi.gammaFactor z)) s := hCongruent
    _ = logDeriv (fun z : Complex => (N : Complex) ^ (z / 2)) s +
        logDeriv (fun z : Complex => chi.LFunction z * chi.gammaFactor z) s :=
      hOuter
    _ = (Real.log N : Complex) / 2 +
        (logDeriv chi.LFunction s + logDeriv chi.gammaFactor s) := by
      rw [hInner, logDeriv_symmetricNormalization]

end BombieriVinogradov.SiegelWalfisz
