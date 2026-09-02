import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedProductFormula
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.GammaFactorRegularity
import Mathlib.Analysis.Analytic.Order

/-!
# Analytic order of the completed Dirichlet L-function

In the positive half-plane the normalization and gamma factors are analytic and
nonvanishing, so completing a nonprincipal Dirichlet L-function does not change
the analytic order at a point.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem analyticOrderNatAt_symmetricCompletedLFunction_eq_LFunction
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : chi ≠ 1) {s : Complex} (hs : 0 < s.re) :
    analyticOrderNatAt (symmetricCompletedLFunction chi) s =
      analyticOrderNatAt chi.LFunction s := by
  have hHalfPlane : {z : Complex | 0 < z.re} ∈ nhds s :=
    (Complex.continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds hs
  have hEventually :
      symmetricCompletedLFunction chi =ᶠ[nhds s]
        fun z : Complex =>
          (N : Complex) ^ (z / 2) *
            (chi.LFunction z * chi.gammaFactor z) := by
    filter_upwards [hHalfPlane] with z hz
    rw [symmetricCompletedLFunction,
      DirichletCharacter.completedLFunction_eq_LFunction_mul_gammaFactor_of_re_pos
        chi hz]
  have hN : (N : Complex) ≠ 0 := by
    exact_mod_cast NeZero.ne N
  have hNormalizationAnalytic :
      AnalyticAt Complex (fun z : Complex => (N : Complex) ^ (z / 2)) s :=
    ((differentiable_id.div_const (2 : Complex)).const_cpow (.inl hN)).analyticAt s
  have hLFunctionAnalytic : AnalyticAt Complex chi.LFunction s :=
    (DirichletCharacter.differentiable_LFunction hchi).analyticAt s
  have hGammaAnalytic : AnalyticAt Complex chi.gammaFactor s := by
    rw [Complex.analyticAt_iff_eventually_differentiableAt]
    filter_upwards [hHalfPlane] with z hz
    exact DirichletCharacter.differentiableAt_gammaFactor_of_re_pos chi hz
  have hNormalizationNe : (N : Complex) ^ (s / 2) ≠ 0 := by
    simp [hN]
  have hGammaNe : chi.gammaFactor s ≠ 0 :=
    DirichletCharacter.gammaFactor_ne_zero_of_re_pos chi hs
  have hNormalizationOrder :
      analyticOrderAt (fun z : Complex => (N : Complex) ^ (z / 2)) s = 0 :=
    hNormalizationAnalytic.analyticOrderAt_eq_zero.mpr hNormalizationNe
  have hGammaOrder : analyticOrderAt chi.gammaFactor s = 0 :=
    hGammaAnalytic.analyticOrderAt_eq_zero.mpr hGammaNe
  have hProductOrder :
      analyticOrderAt
          (fun z : Complex =>
            (N : Complex) ^ (z / 2) *
              (chi.LFunction z * chi.gammaFactor z)) s =
        analyticOrderAt chi.LFunction s := by
    change analyticOrderAt
        ((fun z : Complex => (N : Complex) ^ (z / 2)) *
          (chi.LFunction * chi.gammaFactor)) s = _
    rw [analyticOrderAt_mul hNormalizationAnalytic
      (hLFunctionAnalytic.mul hGammaAnalytic)]
    rw [analyticOrderAt_mul hLFunctionAnalytic hGammaAnalytic]
    rw [hNormalizationOrder, hGammaOrder, zero_add, add_zero]
  have hProductOrderNat :
      analyticOrderNatAt
          (fun z : Complex =>
            (N : Complex) ^ (z / 2) *
              (chi.LFunction z * chi.gammaFactor z)) s =
        analyticOrderNatAt chi.LFunction s := by
    simpa [analyticOrderNatAt] using congrArg ENat.toNat hProductOrder
  have hCompletedOrderNat :
      analyticOrderNatAt (symmetricCompletedLFunction chi) s =
        analyticOrderNatAt
          (fun z : Complex =>
            (N : Complex) ^ (z / 2) *
              (chi.LFunction z * chi.gammaFactor z)) s := by
    simpa [analyticOrderNatAt] using
      congrArg ENat.toNat (analyticOrderAt_congr hEventually)
  exact hCompletedOrderNat.trans hProductOrderNat

end BombieriVinogradov.SiegelWalfisz
