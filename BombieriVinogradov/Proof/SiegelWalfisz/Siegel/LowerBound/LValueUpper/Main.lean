import BombieriVinogradov.Proof.SiegelWalfisz.Siegel.LowerBound.LValueUpper.SeriesBound
import BombieriVinogradov.Proof.SiegelWalfisz.SiegelProduct.Cauchy.LFunctionBlockEquality

/-!
# Logarithmic upper bound for L-values at one

This module combines the initial harmonic block with the uniformly summable
positive-index blocks.
-/

set_option autoImplicit false

open Metric Set

namespace BombieriVinogradov.SiegelWalfisz

noncomputable def characterLLogBoundConstant : ℝ :=
  2 + characterLTailConstant

theorem characterLLogBoundConstant_pos : 0 < characterLLogBoundConstant := by
  rw [characterLLogBoundConstant]
  linarith [characterLTailConstant_nonneg]

theorem norm_LFunction_one_le_log {N : ℕ} [NeZero N]
    (chi : DirichletCharacter ℂ N) (hchi : chi ≠ 1) :
    ‖chi.LFunction 1‖ ≤ characterLLogBoundConstant * (1 + Real.log N) := by
  have hs : (1 : ℂ) ∈ siegelAnalyticDomain := by
    rw [siegelAnalyticDomain, mem_ball]
    norm_num [Complex.dist_eq]
  have hlog : 1 ≤ 1 + Real.log N := by
    have hN : (1 : ℝ) ≤ N := by exact_mod_cast NeZero.pos N
    linarith [Real.log_nonneg hN]
  rw [LFunction_eq_characterLBlockSeries chi hchi hs]
  calc
    ‖characterLBlockSeries chi 1‖ ≤
        2 * (1 + Real.log N) + characterLTailConstant :=
      norm_characterLBlockSeries_one_le chi hchi
    _ ≤ characterLLogBoundConstant * (1 + Real.log N) := by
      rw [characterLLogBoundConstant]
      nlinarith [characterLTailConstant_nonneg]

end BombieriVinogradov.SiegelWalfisz
