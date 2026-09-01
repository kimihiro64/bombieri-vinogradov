import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Analytic order under double complex conjugation

This module proves that conjugating both the input and output of a complex analytic
function preserves its local analytic order, with the center conjugated.
-/

set_option autoImplicit false

namespace BombieriVinogradov.ComplexAnalysis

private theorem hasDerivAt_doubleConjugate
    {f : Complex -> Complex} {f' z : Complex}
    (hf : HasDerivAt f f' ((starRingEnd Complex) z)) :
    HasDerivAt
      (fun w : Complex => (starRingEnd Complex) (f ((starRingEnd Complex) w)))
      ((starRingEnd Complex) f') z := by
  rw [hasDerivAt_iff_tendsto_slope] at hf ⊢
  have hConjTendsto : Filter.Tendsto (starRingEnd Complex)
      (nhdsWithin z {z}ᶜ)
      (nhdsWithin ((starRingEnd Complex) z) {(starRingEnd Complex) z}ᶜ) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · exact (Complex.continuous_conj.tendsto z).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with w hw
      intro hEqual
      apply hw
      have := congrArg (starRingEnd Complex) hEqual
      simpa [Complex.conj_conj] using this
  have hComposition :=
    (Complex.continuous_conj.tendsto f').comp (hf.comp hConjTendsto)
  refine Filter.Tendsto.congr (fun u => ?_) hComposition
  simp only [Function.comp_apply, slope_def_field, map_div₀, map_sub,
    Complex.conj_conj]

theorem AnalyticAt.conj_conj
    {f : Complex -> Complex} {z : Complex}
    (hf : AnalyticAt Complex f ((starRingEnd Complex) z)) :
    AnalyticAt Complex
      (fun w : Complex => (starRingEnd Complex) (f ((starRingEnd Complex) w))) z := by
  rw [Complex.analyticAt_iff_eventually_differentiableAt] at hf ⊢
  have hConj : Filter.Tendsto (starRingEnd Complex)
      (nhds z) (nhds ((starRingEnd Complex) z)) :=
    Complex.continuous_conj.tendsto z
  filter_upwards [hConj.eventually hf] with w hw
  exact (hasDerivAt_doubleConjugate hw.hasDerivAt).differentiableAt

theorem AnalyticAt.analyticOrderAt_conj_conj
    {f : Complex -> Complex} {z : Complex}
    (hf : AnalyticAt Complex f ((starRingEnd Complex) z)) :
    analyticOrderAt
        (fun w : Complex => (starRingEnd Complex) (f ((starRingEnd Complex) w))) z =
      analyticOrderAt f ((starRingEnd Complex) z) := by
  have hConjugateAnalytic :=
    BombieriVinogradov.ComplexAnalysis.AnalyticAt.conj_conj hf
  have hConj : Filter.Tendsto (starRingEnd Complex)
      (nhds z) (nhds ((starRingEnd Complex) z)) :=
    Complex.continuous_conj.tendsto z
  cases hOrder : analyticOrderAt f ((starRingEnd Complex) z) with
  | top =>
      rw [analyticOrderAt_eq_top] at hOrder ⊢
      filter_upwards [hConj.eventually hOrder] with w hw
      rw [hw, map_zero]
  | coe n =>
      rw [hf.analyticOrderAt_eq_natCast] at hOrder
      choose g hg hgZero hFactorization using hOrder
      rw [hConjugateAnalytic.analyticOrderAt_eq_natCast]
      refine Exists.intro
        (fun w : Complex => (starRingEnd Complex) (g ((starRingEnd Complex) w))) ?_
      refine And.intro
        (BombieriVinogradov.ComplexAnalysis.AnalyticAt.conj_conj hg)
        (And.intro ?_ ?_)
      · intro hZero
        apply hgZero
        have := congrArg (starRingEnd Complex) hZero
        simpa [Complex.conj_conj] using this
      · filter_upwards [hConj.eventually hFactorization] with w hw
        rw [hw]
        simp only [smul_eq_mul, map_mul, map_pow, map_sub, Complex.conj_conj]

theorem AnalyticAt.analyticOrderNatAt_conj_conj
    {f : Complex -> Complex} {z : Complex}
    (hf : AnalyticAt Complex f ((starRingEnd Complex) z)) :
    analyticOrderNatAt
        (fun w : Complex => (starRingEnd Complex) (f ((starRingEnd Complex) w))) z =
      analyticOrderNatAt f ((starRingEnd Complex) z) := by
  simpa [analyticOrderNatAt] using congrArg ENat.toNat
    (BombieriVinogradov.ComplexAnalysis.AnalyticAt.analyticOrderAt_conj_conj hf)

end BombieriVinogradov.ComplexAnalysis
