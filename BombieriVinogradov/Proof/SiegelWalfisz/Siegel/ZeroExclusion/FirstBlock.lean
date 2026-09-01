import BombieriVinogradov.Proof.SiegelWalfisz.Siegel.ZeroExclusion.FirstBlockHarmonic
import BombieriVinogradov.Proof.SiegelWalfisz.Siegel.ZeroExclusion.ModulusFactor
import BombieriVinogradov.Proof.SiegelWalfisz.SiegelProduct.Cauchy.CharacterBlocks

/-!
# Initial complete-block bound near one

This module bounds the initial character block throughout the narrow complex
neighborhood used for zero exclusion.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem norm_characterLBlock_zero_near_one_le {N : ℕ} [NeZero N]
    (chi : DirichletCharacter ℂ N) (hchi : Ne chi 1) {s : ℂ}
    (hre : 1 - 1 / (8 * (1 + Real.log N)) ≤ s.re) :
    ‖characterLBlock chi 0 s‖ ≤
      2 * Real.exp (1 / 8 : ℝ) * (1 + Real.log N) := by
  have hNOne : Ne N 1 := by
    intro h
    subst N
    exact hchi (Subsingleton.elim _ _)
  rw [characterLBlock]
  calc
    ‖∑ j : ZMod N, chi j * (((0 * N + j.val : ℕ) : ℂ) ^ (-s))‖ ≤
        ∑ j : ZMod N, ‖chi j * (((0 * N + j.val : ℕ) : ℂ) ^ (-s))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ j : ZMod N, Real.exp (1 / 8 : ℝ) * (j.val : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro j hj
      by_cases hj0 : j = 0
      · subst j
        rw [chi.map_zero' hNOne]
        simp
      · have hjv : Ne j.val 0 := (ZMod.val_ne_zero j).mpr hj0
        have hjpos : (0 : ℝ) < j.val := by exact_mod_cast Nat.pos_of_ne_zero hjv
        have hjN : j.val ≤ N := j.val_lt.le
        have hfactor := submodulus_rpow_one_sub_re_le
          (Nat.pos_of_ne_zero hjv) hjN hre
        have hpower : (j.val : ℝ) ^ (-s.re) ≤
            Real.exp (1 / 8 : ℝ) * (j.val : ℝ)⁻¹ := by
          rw [show -s.re = (1 - s.re) + (-1 : ℝ) by ring,
            Real.rpow_add hjpos, Real.rpow_neg_one]
          exact mul_le_mul_of_nonneg_right hfactor (inv_nonneg.mpr hjpos.le)
        rw [norm_mul]
        calc
          ‖chi j‖ * ‖((0 * N + j.val : ℕ) : ℂ) ^ (-s)‖ ≤
              1 * ‖(j.val : ℂ) ^ (-s)‖ := by
            norm_num only [Nat.zero_mul, Nat.zero_add]
            exact mul_le_mul_of_nonneg_right (chi.norm_le_one j) (norm_nonneg _)
          _ = (j.val : ℝ) ^ (-s.re) := by
            rw [one_mul]
            change ‖((j.val : ℝ) : ℂ) ^ (-s)‖ = (j.val : ℝ) ^ (-s.re)
            rw [Complex.norm_cpow_eq_rpow_re_of_pos hjpos]
            norm_num
          _ ≤ Real.exp (1 / 8 : ℝ) * (j.val : ℝ)⁻¹ := hpower
    _ = Real.exp (1 / 8 : ℝ) * ∑ j : ZMod N, (j.val : ℝ)⁻¹ := by
      rw [Finset.mul_sum]
    _ ≤ Real.exp (1 / 8 : ℝ) * (2 * (harmonic N : ℝ)) :=
      mul_le_mul_of_nonneg_left (sum_zmod_val_inv_le_harmonic N) (Real.exp_nonneg _)
    _ ≤ Real.exp (1 / 8 : ℝ) * (2 * (1 + Real.log N)) := by
      gcongr
      exact harmonic_le_one_add_log N
    _ = 2 * Real.exp (1 / 8 : ℝ) * (1 + Real.log N) := by ring

end BombieriVinogradov.SiegelWalfisz
