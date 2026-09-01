import BombieriVinogradov.Proof.SiegelWalfisz.SiegelProduct.Cauchy.LFunctionBlockEquality

/-!
# Uniform polynomial Dirichlet L-function bound

This module extracts one absolute positive constant from the summable block
majorant and bounds every nonprincipal character L-function by that constant
times the square of its modulus.
-/

set_option autoImplicit false

open Metric Set

namespace BombieriVinogradov.SiegelWalfisz

noncomputable def characterLAbsoluteMajorant (k : ℕ) : ℝ :=
  (15 / 4 : ℝ) * ((k + 1 : ℕ) : ℝ) ^ (-5 / 4 : ℝ)

noncomputable def characterLBoundConstant : ℝ :=
  1 + ∑' k : ℕ, characterLAbsoluteMajorant k

theorem characterLBoundConstant_pos : 0 < characterLBoundConstant := by
  have hnon : 0 ≤ ∑' k : ℕ, characterLAbsoluteMajorant k := by
    apply tsum_nonneg
    intro k
    rw [characterLAbsoluteMajorant]
    positivity
  rw [characterLBoundConstant]
  linarith

theorem norm_LFunction_le_square_on_analyticDomain {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) {s : ℂ}
    (hs : s ∈ siegelAnalyticDomain) :
    ‖χ.LFunction s‖ ≤ characterLBoundConstant * (N : ℝ) ^ 2 := by
  rw [LFunction_eq_characterLBlockSeries χ hχ hs]
  apply (norm_characterLBlockSeries_le χ hχ hs).trans
  calc
    ∑' k : ℕ, characterLBlockMajorant N k =
        (N : ℝ) ^ 2 * ∑' k : ℕ, characterLAbsoluteMajorant k := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro k
      rw [characterLAbsoluteMajorant, characterLBlockMajorant]
      ring
    _ ≤ characterLBoundConstant * (N : ℝ) ^ 2 := by
      rw [mul_comm characterLBoundConstant]
      apply mul_le_mul_of_nonneg_left
      · rw [characterLBoundConstant]
        linarith
      · positivity

theorem exists_characterLFunction_circle_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N),
      χ ≠ 1 → ∀ {s : ℂ}, s ∈ siegelCauchyCircle →
        ‖χ.LFunction s‖ ≤ C * (N : ℝ) ^ 2 := by
  exact ⟨characterLBoundConstant, characterLBoundConstant_pos, fun χ hχ s hs ↦
    norm_LFunction_le_square_on_analyticDomain χ hχ
      (siegelCauchyCircle_subset_analyticDomain hs)⟩

theorem norm_LFunction_one_le_square {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) :
    ‖χ.LFunction 1‖ ≤ characterLBoundConstant * (N : ℝ) ^ 2 := by
  apply norm_LFunction_le_square_on_analyticDomain χ hχ
  rw [siegelAnalyticDomain, mem_ball]
  norm_num [Complex.dist_eq]

end BombieriVinogradov.SiegelWalfisz
