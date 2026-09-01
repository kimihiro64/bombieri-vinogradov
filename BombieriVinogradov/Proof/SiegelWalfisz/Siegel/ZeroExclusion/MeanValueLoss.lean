import BombieriVinogradov.Proof.SiegelWalfisz.Siegel.ZeroExclusion.DerivativeBound
import Mathlib.Analysis.Complex.RealDeriv

/-!
# Mean-value loss for a Dirichlet L-function near one

This module converts the uniform complex derivative bound into a lower bound
for the real part along the real interval ending at one.
-/

set_option autoImplicit false

open Set

namespace BombieriVinogradov.SiegelWalfisz

theorem LFunction_re_lower_of_near_one {N : ℕ} [NeZero N]
    (chi : DirichletCharacter ℂ N) (hchi : Ne chi 1) {t : ℝ}
    (htLower : 1 - zeroExclusionRadius N ≤ t) (htUpper : t ≤ 1) :
    (chi.LFunction 1).re -
        characterLDerivativeBoundConstant * (1 + Real.log N) ^ 2 * (1 - t) ≤
      (chi.LFunction t).re := by
  have hderiv (u : ℝ) (hu : u ∈ Icc t 1) :
      HasDerivWithinAt (fun v : ℝ ↦ (chi.LFunction v).re)
        (deriv chi.LFunction u).re (Icc t 1) u := by
    exact ((chi.differentiable_LFunction hchi u).hasDerivAt.real_of_complex).hasDerivWithinAt
  have hbound (u : ℝ) (hu : u ∈ Icc t 1) :
      |(deriv chi.LFunction u).re| ≤
        characterLDerivativeBoundConstant * (1 + Real.log N) ^ 2 := by
    exact (Complex.abs_re_le_norm (deriv chi.LFunction u)).trans
      (norm_deriv_LFunction_near_one_le chi hchi (htLower.trans hu.1) hu.2)
  have hmv := (convex_Icc t 1 : Convex ℝ (Icc t 1)).norm_image_sub_le_of_norm_hasDerivWithin_le
    hderiv hbound (left_mem_Icc.mpr htUpper) (right_mem_Icc.mpr htUpper)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr htUpper)] at hmv
  have hdiff :
      (chi.LFunction 1).re - (chi.LFunction t).re ≤
        characterLDerivativeBoundConstant * (1 + Real.log N) ^ 2 * (1 - t) := by
    exact (le_abs_self _).trans hmv
  linarith

end BombieriVinogradov.SiegelWalfisz
