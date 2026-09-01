import BombieriVinogradov.Proof.SiegelWalfisz.SiegelProduct.Cauchy.CharacterBlocks
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Initial character block at one

This module bounds the initial complete Dirichlet-character block by a
harmonic sum and then by a logarithm.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

private theorem sum_zmod_val_inv_le_harmonic (N : ℕ) [NeZero N] :
    ∑ j : ZMod N, ((j.val : ℝ)⁻¹) ≤ 2 * (harmonic N : ℝ) := by
  calc
    ∑ j : ZMod N, ((j.val : ℝ)⁻¹) = ∑ i : Fin N, ((i.val : ℝ)⁻¹) := by
      symm
      apply Fintype.sum_equiv (ZMod.finEquiv N).toEquiv
      intro i
      change ((i.val : ℝ)⁻¹) = ((((ZMod.finEquiv N) i).val : ℝ)⁻¹)
      congr 2
      obtain _ | n := N
      · exact (NeZero.ne 0 rfl).elim
      · rfl
    _ ≤ ∑ i : Fin N, 2 * ((((i.val + 1 : ℕ) : ℝ))⁻¹) := by
      apply Finset.sum_le_sum
      intro i hi
      by_cases hi0 : i.val = 0
      · simp [hi0]
      · have hipos : (0 : ℝ) < i.val := by exact_mod_cast Nat.pos_of_ne_zero hi0
        have hisucc : (0 : ℝ) < i.val + 1 := by positivity
        rw [← one_div, ← div_eq_mul_inv]
        norm_num only [Nat.cast_add, Nat.cast_one]
        rw [div_le_div_iff₀ hipos hisucc]
        norm_num
        have hiNat : i.val + 1 ≤ 2 * i.val := by omega
        exact_mod_cast hiNat
    _ = 2 * (harmonic N : ℝ) := by
      rw [← Finset.mul_sum]
      congr 1
      rw [Finset.sum_fin_eq_sum_range, harmonic, Rat.cast_sum]
      apply Finset.sum_congr rfl
      intro x hx
      simp [Finset.mem_range.mp hx]

theorem norm_characterLBlock_zero_one_le {N : ℕ} [NeZero N]
    (chi : DirichletCharacter ℂ N) (hchi : chi ≠ 1) :
    ‖characterLBlock chi 0 1‖ ≤ 2 * (1 + Real.log N) := by
  have hN : N ≠ 1 := by
    intro h
    subst N
    exact hchi (Subsingleton.elim _ _)
  rw [characterLBlock]
  calc
    ‖∑ j : ZMod N, chi j * (((0 * N + j.val : ℕ) : ℂ) ^ (-(1 : ℂ)))‖ ≤
        ∑ j : ZMod N, ‖chi j * (((0 * N + j.val : ℕ) : ℂ) ^ (-(1 : ℂ)))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ j : ZMod N, ((j.val : ℝ)⁻¹) := by
      apply Finset.sum_le_sum
      intro j hj
      by_cases hj0 : j = 0
      · subst j
        rw [chi.map_zero' hN]
        simp
      · have hjv : j.val ≠ 0 := (ZMod.val_ne_zero j).mpr hj0
        rw [norm_mul]
        calc
          ‖chi j‖ * ‖((0 * N + j.val : ℕ) : ℂ) ^ (-(1 : ℂ))‖ ≤
              1 * ‖((j.val : ℕ) : ℂ) ^ (-(1 : ℂ))‖ := by
            norm_num only [Nat.zero_mul, Nat.zero_add]
            exact mul_le_mul_of_nonneg_right (chi.norm_le_one j) (norm_nonneg _)
          _ = ((j.val : ℝ)⁻¹) := by
            rw [one_mul, show (-(1 : ℂ)) = ((-1 : ℝ) : ℂ) by norm_num,
              ← Complex.ofReal_natCast j.val,
              ← Complex.ofReal_cpow (Nat.cast_nonneg j.val) (-1), Complex.norm_real,
              Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg j.val) _),
              Real.rpow_neg_one]
    _ ≤ 2 * (harmonic N : ℝ) := sum_zmod_val_inv_le_harmonic N
    _ ≤ 2 * (1 + Real.log N) := by
      gcongr
      exact harmonic_le_one_add_log N

end BombieriVinogradov.SiegelWalfisz
