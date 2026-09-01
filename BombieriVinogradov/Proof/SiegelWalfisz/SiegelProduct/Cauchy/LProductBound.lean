import BombieriVinogradov.Proof.SiegelWalfisz.SiegelProduct.Cauchy.ResidueBound

/-!
# Uniform bound for the three-factor L-product

This module owns the polynomial estimate for the analytic L-product on the
source Cauchy circle.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem norm_siegelLProduct_le {N M : ℕ} [NeZero N] [NeZero M]
    [NeZero (N.lcm M)] (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M)
    (hχ : χ ≠ 1) (hψ : ψ ≠ 1) (hmul : DirichletCharacter.mul χ ψ ≠ 1)
    {s : ℂ} (hs : s ∈ siegelCauchyCircle) :
    ‖siegelLProduct χ ψ s‖ ≤
      siegelResidueBoundConstant * ((N : ℝ) * (M : ℝ)) ^ 4 := by
  have hsDomain := siegelCauchyCircle_subset_analyticDomain hs
  have hχb := norm_LFunction_le_square_on_analyticDomain χ hχ hsDomain
  have hψb := norm_LFunction_le_square_on_analyticDomain ψ hψ hsDomain
  have hmulb := norm_LFunction_le_square_on_analyticDomain
    (DirichletCharacter.mul χ ψ) hmul hsDomain
  have hC : 0 ≤ characterLBoundConstant := characterLBoundConstant_pos.le
  have hNMpos : 0 < N * M := Nat.mul_pos (NeZero.pos N) (NeZero.pos M)
  have hlcmNat : N.lcm M ≤ N * M := Nat.le_of_dvd hNMpos (Nat.lcm_dvd_mul N M)
  have hlcm : ((N.lcm M : ℕ) : ℝ) ≤ (N : ℝ) * (M : ℝ) := by
    exact_mod_cast hlcmNat
  have hlcmSq : ((N.lcm M : ℕ) : ℝ) ^ 2 ≤ ((N : ℝ) * (M : ℝ)) ^ 2 := by
    gcongr
  rw [siegelLProduct, norm_mul, norm_mul]
  calc
    ‖χ.LFunction s‖ * ‖ψ.LFunction s‖ * ‖(DirichletCharacter.mul χ ψ).LFunction s‖
        ≤ (characterLBoundConstant * (N : ℝ) ^ 2) *
            (characterLBoundConstant * (M : ℝ) ^ 2) *
              (characterLBoundConstant * ((N.lcm M : ℕ) : ℝ) ^ 2) := by
      have hχψ : ‖χ.LFunction s‖ * ‖ψ.LFunction s‖ ≤
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
