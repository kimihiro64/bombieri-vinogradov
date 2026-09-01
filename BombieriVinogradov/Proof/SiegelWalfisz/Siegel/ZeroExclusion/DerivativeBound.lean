import BombieriVinogradov.Proof.SiegelWalfisz.Siegel.ZeroExclusion.DerivativeConstant
import BombieriVinogradov.Proof.SiegelWalfisz.Siegel.ZeroExclusion.LFunctionBound
import BombieriVinogradov.Proof.SiegelWalfisz.Siegel.ZeroExclusion.SphereGeometry
import Mathlib.Analysis.Complex.Liouville

/-!
# Uniform near-one derivative bound for Dirichlet L-functions

This module applies Cauchy's derivative estimate on the compiled near-one
sphere and obtains an absolute multiple of `(1 + log N)^2`.
-/

set_option autoImplicit false

open Metric

namespace BombieriVinogradov.SiegelWalfisz

theorem norm_deriv_LFunction_near_one_le {N : ℕ} [NeZero N]
    (chi : DirichletCharacter ℂ N) (hchi : Ne chi 1) {t : ℝ}
    (htLower : 1 - zeroExclusionRadius N ≤ t) (htUpper : t ≤ 1) :
    ‖deriv chi.LFunction t‖ ≤
      characterLDerivativeBoundConstant * (1 + Real.log N) ^ 2 := by
  have hrPos : 0 < zeroExclusionRadius N := zeroExclusionRadius_pos
  have hvalue (z : ℂ) (hz : z ∈ sphere (t : ℂ) (zeroExclusionRadius N)) :
      ‖chi.LFunction z‖ ≤ characterLNearOneBoundConstant * (1 + Real.log N) := by
    obtain ⟨hzDomain, hzSharp, hzSeven, hzNorm⟩ :=
      zeroExclusionSphere_geometry htLower htUpper hz
    exact norm_LFunction_near_one_le chi hchi hzDomain hzSharp hzSeven hzNorm
  have hcauchy := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hrPos
    (chi.differentiable_LFunction hchi).diffContOnCl hvalue
  calc
    ‖deriv chi.LFunction t‖ ≤
        (characterLNearOneBoundConstant * (1 + Real.log N)) /
          zeroExclusionRadius N := hcauchy
    _ = characterLDerivativeBoundConstant * (1 + Real.log N) ^ 2 := by
      have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast NeZero.pos N
      have hlog : 0 ≤ Real.log N := Real.log_nonneg hNreal
      have hlogOne : Ne (1 + Real.log N) 0 := by linarith
      unfold zeroExclusionRadius characterLDerivativeBoundConstant
      field_simp

end BombieriVinogradov.SiegelWalfisz
