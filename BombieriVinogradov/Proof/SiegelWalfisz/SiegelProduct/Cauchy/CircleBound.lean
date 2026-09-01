import BombieriVinogradov.Proof.SiegelWalfisz.SiegelProduct.Cauchy.LProductBound
import BombieriVinogradov.Proof.SiegelWalfisz.SiegelProduct.Cauchy.ZetaBound
import BombieriVinogradov.Proof.SiegelWalfisz.SiegelProduct.Pole.Main

/-!
# Pole-subtracted Siegel-product bound on the source circle

This module composes the separate geometry, zeta, L-product, and residue
interfaces into the uniform polynomial bound required by Cauchy's inequalities.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem siegelPoleSubtracted_circle_bound :
    ∃ C : ℝ, 0 < C ∧ ∃ K : ℕ,
      ∀ {N M : ℕ} [NeZero N] [NeZero M] [NeZero (N.lcm M)]
        (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M),
        χ ≠ 1 → ψ ≠ 1 → DirichletCharacter.mul χ ψ ≠ 1 →
          ∀ {s : ℂ}, s ∈ siegelCauchyCircle →
            ‖siegelPoleSubtracted χ ψ s‖ ≤ C * ((N : ℝ) * (M : ℝ)) ^ K := by
  obtain ⟨Cζ, hCζ, hzeta⟩ := exists_riemannZeta_circle_bound
  refine ⟨(Cζ + 2) * siegelResidueBoundConstant,
    mul_pos (by linarith) siegelResidueBoundConstant_pos, 4, ?_⟩
  intro N M instN instM instLcm χ ψ hχ hψ hmul s hs
  have hL := norm_siegelLProduct_le χ ψ hχ hψ hmul hs
  have hres := norm_siegelProductResidue_le χ ψ hχ hψ hmul
  have hdist := siegelCauchyCircle_norm_sub_one_lower hs
  have hnormpos : 0 < ‖s - 1‖ := lt_of_lt_of_le (by norm_num) hdist
  have hinv : ‖s - 1‖⁻¹ ≤ 2 := by
    have : 1 * ‖s - 1‖⁻¹ ≤ 2 := by
      rw [mul_inv_le_iff₀ hnormpos]
      linarith
    simpa using this
  rw [siegelPoleSubtracted_apply_of_ne χ ψ (siegelCauchyCircle_ne_one hs)]
  calc
    ‖riemannZeta s * siegelLProduct χ ψ s - siegelProductResidue χ ψ / (s - 1)‖
        ≤ ‖riemannZeta s * siegelLProduct χ ψ s‖ +
          ‖siegelProductResidue χ ψ / (s - 1)‖ := norm_sub_le _ _
    _ = ‖riemannZeta s‖ * ‖siegelLProduct χ ψ s‖ +
          ‖siegelProductResidue χ ψ‖ * ‖s - 1‖⁻¹ := by
      rw [norm_mul, norm_div, div_eq_mul_inv]
    _ ≤ Cζ * (siegelResidueBoundConstant * ((N : ℝ) * (M : ℝ)) ^ 4) +
          (siegelResidueBoundConstant * ((N : ℝ) * (M : ℝ)) ^ 4) * 2 := by
      apply add_le_add
      · exact mul_le_mul (hzeta s hs) hL (norm_nonneg _) hCζ.le
      · exact mul_le_mul hres hinv (inv_nonneg.mpr (norm_nonneg _))
          (mul_nonneg siegelResidueBoundConstant_pos.le (pow_nonneg (by positivity) _))
    _ = ((Cζ + 2) * siegelResidueBoundConstant) * ((N : ℝ) * (M : ℝ)) ^ 4 := by
      ring

end BombieriVinogradov.SiegelWalfisz
