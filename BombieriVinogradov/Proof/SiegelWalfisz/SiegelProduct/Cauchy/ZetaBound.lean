import BombieriVinogradov.Proof.SiegelWalfisz.SiegelProduct.Cauchy.Geometry
import BombieriVinogradov.Proof.SiegelWalfisz.SiegelProduct.Pole.ZetaRegularized

/-!
# Regular-zeta bound on the Siegel Cauchy circle

This module extracts one absolute positive bound for the regularized Riemann
zeta factor on the fixed compact circle.
-/

set_option autoImplicit false

open Metric Set

namespace BombieriVinogradov.SiegelWalfisz

theorem exists_zetaRegularized_circle_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ s ∈ siegelCauchyCircle, ‖riemannZeta₀ s‖ ≤ C := by
  obtain ⟨M, hM⟩ := (isCompact_sphere (2 : ℂ) (3 / 2 : ℝ)).bddAbove_image
    zetaRegularized_differentiable.continuous.norm.continuousOn
  refine ⟨max 1 M, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro s hs
  exact (hM (mem_image_of_mem _ hs)).trans (le_max_right _ _)

theorem exists_riemannZeta_circle_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ s ∈ siegelCauchyCircle, ‖riemannZeta s‖ ≤ C := by
  obtain ⟨C, hC, hregular⟩ := exists_zetaRegularized_circle_bound
  refine ⟨2 + C, by linarith, ?_⟩
  intro s hs
  have hdist := siegelCauchyCircle_norm_sub_one_lower hs
  have hnormpos : 0 < ‖s - 1‖ := lt_of_lt_of_le (by norm_num) hdist
  have hinv : ‖(s - 1)⁻¹‖ ≤ 2 := by
    rw [norm_inv]
    have : 1 * ‖s - 1‖⁻¹ ≤ 2 := by
      rw [mul_inv_le_iff₀ hnormpos]
      linarith
    simpa using this
  rw [riemannZeta_eq_pole_add_regularized (siegelCauchyCircle_ne_one hs)]
  exact (norm_add_le _ _).trans ((add_le_add hinv (hregular s hs)).trans_eq (by ring))

end BombieriVinogradov.SiegelWalfisz
