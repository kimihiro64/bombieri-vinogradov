import BombieriVinogradov.Proof.SiegelWalfisz.Siegel.ZeroExclusion.FirstBlock
import BombieriVinogradov.Proof.SiegelWalfisz.Siegel.ZeroExclusion.TailSumBound
import BombieriVinogradov.Proof.SiegelWalfisz.Siegel.ZeroExclusion.ValueConstant

/-!
# Logarithmic bound for the grouped character series near one

This module only composes the compiled initial-block and summed-tail estimates.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem norm_characterLBlockSeries_near_one_le {N : ℕ} [NeZero N]
    (chi : DirichletCharacter ℂ N) (hchi : Ne chi 1) {s : ℂ}
    (hsDomain : s ∈ siegelAnalyticDomain)
    (hre : 1 - 1 / (8 * (1 + Real.log N)) ≤ s.re)
    (hseven : 7 / 8 ≤ s.re) (hnorm : ‖s‖ ≤ 2) :
    ‖characterLBlockSeries chi s‖ ≤
      characterLNearOneBoundConstant * (1 + Real.log N) := by
  have hnormSummable := characterLBlock_norm_summable_on_domain chi hchi hsDomain
  have htail := characterLBlock_tail_near_one_le chi hchi hsDomain hre hseven hnorm
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast NeZero.pos N
  have hlog : 1 ≤ 1 + Real.log N := by linarith [Real.log_nonneg hNreal]
  rw [characterLBlockSeries]
  calc
    ‖∑' k : ℕ, characterLBlock chi k s‖ ≤
        ∑' k : ℕ, ‖characterLBlock chi k s‖ :=
      norm_tsum_le_tsum_norm hnormSummable
    _ = ‖characterLBlock chi 0 s‖ +
        ∑' k : ℕ, ‖characterLBlock chi (k + 1) s‖ := hnormSummable.tsum_eq_zero_add
    _ ≤ 2 * Real.exp (1 / 8 : ℝ) * (1 + Real.log N) +
        2 * Real.exp (1 / 8 : ℝ) * zeroExclusionTailConstant :=
      add_le_add (norm_characterLBlock_zero_near_one_le chi hchi hre) htail
    _ ≤ 2 * Real.exp (1 / 8 : ℝ) * (1 + zeroExclusionTailConstant) *
        (1 + Real.log N) := by
      have htwoExp : 0 ≤ 2 * Real.exp (1 / 8 : ℝ) :=
        mul_nonneg (by norm_num) (Real.exp_nonneg _)
      have htailCoefficient :
          0 ≤ 2 * Real.exp (1 / 8 : ℝ) * zeroExclusionTailConstant :=
        mul_nonneg htwoExp zeroExclusionTailConstant_nonneg
      have htailScaled :
          2 * Real.exp (1 / 8 : ℝ) * zeroExclusionTailConstant ≤
            (2 * Real.exp (1 / 8 : ℝ) * zeroExclusionTailConstant) *
              (1 + Real.log N) :=
        by simpa only [mul_one] using
          mul_le_mul_of_nonneg_left hlog htailCoefficient
      calc
        2 * Real.exp (1 / 8 : ℝ) * (1 + Real.log N) +
            2 * Real.exp (1 / 8 : ℝ) * zeroExclusionTailConstant ≤
          2 * Real.exp (1 / 8 : ℝ) * (1 + Real.log N) +
            (2 * Real.exp (1 / 8 : ℝ) * zeroExclusionTailConstant) *
              (1 + Real.log N) := by
          simpa [add_comm] using
            add_le_add_left htailScaled
              (2 * Real.exp (1 / 8 : ℝ) * (1 + Real.log N))
        _ = 2 * Real.exp (1 / 8 : ℝ) * (1 + zeroExclusionTailConstant) *
            (1 + Real.log N) := by ring
    _ = characterLNearOneBoundConstant * (1 + Real.log N) := by
      rfl

end BombieriVinogradov.SiegelWalfisz
