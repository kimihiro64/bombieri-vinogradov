import BombieriVinogradov.Proof.SiegelWalfisz.SiegelProduct.Cauchy.CharacterBlockBound
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.PSeries

/-!
# Analytic grouped character series

This module owns summability of the block majorant, holomorphy of the grouped
series, and its uniform norm bound on the fixed analytic domain.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

/-- The conditionally continued character series grouped into complete residue blocks. -/
noncomputable def characterLBlockSeries {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (s : ℂ) : ℂ :=
  ∑' k : ℕ, characterLBlock χ k s

theorem characterLBlockMajorant_summable (N : ℕ) :
    Summable (characterLBlockMajorant N) := by
  have hp : Summable (fun n : ℕ ↦ (n : ℝ) ^ (-5 / 4 : ℝ)) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  have hshift := (summable_nat_add_iff 1).mpr hp
  change Summable (fun k : ℕ ↦
    (15 / 4 : ℝ) * (N : ℝ) ^ 2 * ((k + 1 : ℕ) : ℝ) ^ (-5 / 4 : ℝ))
  exact hshift.mul_left ((15 / 4 : ℝ) * (N : ℝ) ^ 2)

theorem characterLBlockSeries_differentiableOn {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) :
    DifferentiableOn ℂ (characterLBlockSeries χ) siegelAnalyticDomain := by
  change DifferentiableOn ℂ (fun s ↦ ∑' k : ℕ, characterLBlock χ k s)
    siegelAnalyticDomain
  exact Complex.differentiableOn_tsum_of_summable_norm
    (characterLBlockMajorant_summable N)
    (fun k ↦ characterLBlock_differentiableOn χ hχ k)
    (by exact Metric.isOpen_ball)
    (fun k s hs ↦ norm_characterLBlock_le χ hχ k hs)

theorem norm_characterLBlockSeries_le {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) {s : ℂ}
    (hs : s ∈ siegelAnalyticDomain) :
    ‖characterLBlockSeries χ s‖ ≤ ∑' k : ℕ, characterLBlockMajorant N k := by
  rw [characterLBlockSeries]
  exact tsum_of_norm_bounded (characterLBlockMajorant_summable N).hasSum
    (fun k ↦ norm_characterLBlock_le χ hχ k hs)

end BombieriVinogradov.SiegelWalfisz
