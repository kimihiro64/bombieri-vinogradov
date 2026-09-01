import BombieriVinogradov.Proof.SiegelWalfisz.Siegel.ZeroExclusion.TailComparison
import BombieriVinogradov.Proof.SiegelWalfisz.Siegel.ZeroExclusion.TailPointwise
import BombieriVinogradov.Proof.SiegelWalfisz.Siegel.ZeroExclusion.TailSummability

/-!
# Summed character-block tail near one

This module compares the character-dependent positive-index blocks with the
fixed scalar tail series.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem characterLBlock_tail_near_one_le {N : ℕ} [NeZero N]
    (chi : DirichletCharacter ℂ N) (hchi : Ne chi 1) {s : ℂ}
    (hsDomain : s ∈ siegelAnalyticDomain)
    (hre : 1 - 1 / (8 * (1 + Real.log N)) ≤ s.re)
    (hseven : 7 / 8 ≤ s.re) (hnorm : ‖s‖ ≤ 2) :
    ∑' k : ℕ, ‖characterLBlock chi (k + 1) s‖ ≤
      2 * Real.exp (1 / 8 : ℝ) * zeroExclusionTailConstant := by
  exact tsum_le_zeroExclusionTail
    (characterLBlock_tail_norm_summable chi hchi hsDomain)
    (norm_characterLBlock_tail_shifted_le chi hchi hre hseven hnorm)

end BombieriVinogradov.SiegelWalfisz
