import BombieriVinogradov.Proof.SiegelWalfisz.Siegel.ZeroExclusion.SeriesBound
import BombieriVinogradov.Proof.SiegelWalfisz.SiegelProduct.Cauchy.LFunctionBlockEquality

/-!
# Logarithmic L-function bound near one

This module transports the grouped-series estimate to Mathlib's analytically
continued Dirichlet L-function.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem norm_LFunction_near_one_le {N : ℕ} [NeZero N]
    (chi : DirichletCharacter ℂ N) (hchi : Ne chi 1) {s : ℂ}
    (hsDomain : s ∈ siegelAnalyticDomain)
    (hre : 1 - 1 / (8 * (1 + Real.log N)) ≤ s.re)
    (hseven : 7 / 8 ≤ s.re) (hnorm : ‖s‖ ≤ 2) :
    ‖chi.LFunction s‖ ≤ characterLNearOneBoundConstant * (1 + Real.log N) := by
  rw [LFunction_eq_characterLBlockSeries chi hchi hsDomain]
  exact norm_characterLBlockSeries_near_one_le chi hchi hsDomain hre hseven hnorm

end BombieriVinogradov.SiegelWalfisz
