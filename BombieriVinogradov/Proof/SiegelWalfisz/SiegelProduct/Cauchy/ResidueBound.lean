import BombieriVinogradov.Proof.SiegelWalfisz.SiegelProduct.Cauchy.LFunctionBound
import BombieriVinogradov.Proof.SiegelWalfisz.SiegelProduct.Pole.Product

/-!
# Uniform Siegel-product residue bound

This module owns the polynomial estimate for the residue of the four-factor
Siegel product at one.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

noncomputable def siegelResidueBoundConstant : ℝ := characterLBoundConstant ^ 3

theorem siegelResidueBoundConstant_pos : 0 < siegelResidueBoundConstant := by
  rw [siegelResidueBoundConstant]
  exact pow_pos characterLBoundConstant_pos 3

theorem norm_siegelProductResidue_le {N M : ℕ} [NeZero N] [NeZero M]
    [NeZero (N.lcm M)] (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M)
    (hχ : χ ≠ 1) (hψ : ψ ≠ 1) (hmul : DirichletCharacter.mul χ ψ ≠ 1) :
    ‖siegelProductResidue χ ψ‖ ≤
      siegelResidueBoundConstant * ((N : ℝ) * (M : ℝ)) ^ 4 := by
  have hχb := norm_LFunction_one_le_square χ hχ
  have hψb := norm_LFunction_one_le_square ψ hψ
  have hmulb := norm_LFunction_one_le_square (DirichletCharacter.mul χ ψ) hmul
  have hC : 0 ≤ characterLBoundConstant := characterLBoundConstant_pos.le
  have hNMpos : 0 < N * M := Nat.mul_pos (NeZero.pos N) (NeZero.pos M)
  have hlcmNat : N.lcm M ≤ N * M := Nat.le_of_dvd hNMpos (Nat.lcm_dvd_mul N M)
  have hlcm : ((N.lcm M : ℕ) : ℝ) ≤ (N : ℝ) * (M : ℝ) := by
    exact_mod_cast hlcmNat
  have hlcmSq : ((N.lcm M : ℕ) : ℝ) ^ 2 ≤ ((N : ℝ) * (M : ℝ)) ^ 2 := by
    gcongr
  rw [siegelProductResidue, norm_mul, norm_mul]
  calc
    ‖χ.LFunction 1‖ * ‖ψ.LFunction 1‖ * ‖(DirichletCharacter.mul χ ψ).LFunction 1‖
        ≤ (characterLBoundConstant * (N : ℝ) ^ 2) *
            (characterLBoundConstant * (M : ℝ) ^ 2) *
              (characterLBoundConstant * ((N.lcm M : ℕ) : ℝ) ^ 2) := by
      have hχψ : ‖χ.LFunction 1‖ * ‖ψ.LFunction 1‖ ≤
          (characterLBoundConstant * (N : ℝ) ^ 2) *
            (characterLBoundConstant * (M : ℝ) ^ 2) := by
        exact mul_le_mul hχb hψb (norm_nonneg _) (mul_nonneg hC (sq_nonneg _))
      exact mul_le_mul hχψ hmulb (norm_nonneg _) (mul_nonneg
        (mul_nonneg hC (sq_nonneg _)) (mul_nonneg hC (sq_nonneg _)))
    _ = characterLBoundConstant ^ 3 * ((N : ℝ) * (M : ℝ)) ^ 2 *
          ((N.lcm M : ℕ) : ℝ) ^ 2 := by ring
    _ ≤ characterLBoundConstant ^ 3 * ((N : ℝ) * (M : ℝ)) ^ 2 *
          ((N : ℝ) * (M : ℝ)) ^ 2 := by
      exact mul_le_mul_of_nonneg_left hlcmSq
        (mul_nonneg (pow_nonneg hC _) (sq_nonneg _))
    _ = siegelResidueBoundConstant * ((N : ℝ) * (M : ℝ)) ^ 4 := by
      rw [siegelResidueBoundConstant]
      ring

end BombieriVinogradov.SiegelWalfisz
