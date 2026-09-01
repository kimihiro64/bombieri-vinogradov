import BombieriVinogradov.Proof.SiegelWalfisz.Siegel.LowerBound.LValueUpper.FirstBlock
import BombieriVinogradov.Proof.SiegelWalfisz.Siegel.LowerBound.LValueUpper.TailBlock
import BombieriVinogradov.Proof.SiegelWalfisz.SiegelProduct.Cauchy.CharacterBlockSeries
import Mathlib.Analysis.PSeries

/-!
# Assembly of the character-block estimate

This module sums the pointwise positive-index block bounds and combines them
with the initial harmonic block.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

noncomputable def characterLTailConstant : ℝ :=
  ∑' k : ℕ, ((((k + 1 : ℕ) : ℝ) ^ 2)⁻¹)

theorem characterLTail_summable :
    Summable (fun k : ℕ ↦ ((((k + 1 : ℕ) : ℝ) ^ 2)⁻¹)) := by
  have hp : Summable (fun k : ℕ ↦ (((k : ℝ) ^ 2)⁻¹)) :=
    Real.summable_nat_pow_inv.mpr (by norm_num)
  exact (summable_nat_add_iff 1).mpr hp

theorem characterLTailConstant_nonneg : 0 ≤ characterLTailConstant := by
  rw [characterLTailConstant]
  exact tsum_nonneg fun k ↦ by positivity

theorem characterLBlock_one_norm_summable {N : ℕ} [NeZero N]
    (chi : DirichletCharacter ℂ N) (hchi : chi ≠ 1) :
    Summable (fun k : ℕ ↦ ‖characterLBlock chi k 1‖) := by
  have hs : (1 : ℂ) ∈ siegelAnalyticDomain := by
    rw [siegelAnalyticDomain, Metric.mem_ball]
    norm_num [Complex.dist_eq]
  exact (characterLBlockMajorant_summable N).of_nonneg_of_le
    (fun k ↦ norm_nonneg _) fun k ↦ norm_characterLBlock_le chi hchi k hs

set_option maxHeartbeats 800000 in
theorem characterLBlock_tail_norm_le {N : ℕ} [NeZero N]
    (chi : DirichletCharacter ℂ N) (hchi : chi ≠ 1) :
    ∑' k : ℕ, ‖characterLBlock chi (k + 1) 1‖ ≤ characterLTailConstant := by
  have hnorm := characterLBlock_one_norm_summable chi hchi
  have htailNorm : Summable (fun k : ℕ ↦ ‖characterLBlock chi (k + 1) 1‖) :=
    (summable_nat_add_iff 1).mpr hnorm
  rw [characterLTailConstant]
  exact htailNorm.tsum_le_tsum
    (fun k ↦ norm_characterLBlock_one_le chi hchi (Nat.le_add_left 1 k))
    characterLTail_summable

theorem norm_characterLBlockSeries_one_le {N : ℕ} [NeZero N]
    (chi : DirichletCharacter ℂ N) (hchi : chi ≠ 1) :
    ‖characterLBlockSeries chi 1‖ ≤
      2 * (1 + Real.log N) + characterLTailConstant := by
  have hnorm := characterLBlock_one_norm_summable chi hchi
  rw [characterLBlockSeries]
  calc
    ‖∑' k : ℕ, characterLBlock chi k 1‖ ≤
        ∑' k : ℕ, ‖characterLBlock chi k 1‖ :=
      norm_tsum_le_tsum_norm hnorm
    _ = ‖characterLBlock chi 0 1‖ +
        ∑' k : ℕ, ‖characterLBlock chi (k + 1) 1‖ := hnorm.tsum_eq_zero_add
    _ ≤ 2 * (1 + Real.log N) + characterLTailConstant :=
      add_le_add (norm_characterLBlock_zero_one_le chi hchi)
        (characterLBlock_tail_norm_le chi hchi)

end BombieriVinogradov.SiegelWalfisz
