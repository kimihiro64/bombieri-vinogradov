import BombieriVinogradov.Proof.SiegelWalfisz.Siegel.LowerBound.LValueUpper.ReciprocalVariation
import BombieriVinogradov.Proof.SiegelWalfisz.SiegelProduct.Cauchy.CharacterBlocks

/-!
# Complete-block bound at one

This module bounds every positive-index complete character block by the
summable majorant `1 / k^2`, uniformly in the character modulus.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem norm_characterLBlock_one_le {N : ℕ} [NeZero N]
    (chi : DirichletCharacter ℂ N) (hchi : chi ≠ 1) {k : ℕ} (hk : 1 ≤ k) :
    ‖characterLBlock chi k 1‖ ≤ ((k : ℝ) ^ 2)⁻¹ := by
  have hN : N ≠ 1 := by
    intro h
    subst N
    exact hchi (Subsingleton.elim _ _)
  rw [characterLBlock_recenter chi hchi]
  calc
    ‖∑ j : ZMod N, chi j *
        (((k * N + j.val : ℕ) : ℂ) ^ (-(1 : ℂ)) -
          (((k + 1) * N : ℕ) : ℂ) ^ (-(1 : ℂ)))‖ ≤
        ∑ j : ZMod N, ‖chi j *
          (((k * N + j.val : ℕ) : ℂ) ^ (-(1 : ℂ)) -
            (((k + 1) * N : ℕ) : ℂ) ^ (-(1 : ℂ)))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _j : ZMod N, (((k : ℝ) ^ 2) * (N : ℝ))⁻¹ := by
      apply Finset.sum_le_sum
      intro j hj
      by_cases hj0 : j = 0
      · subst j
        rw [chi.map_zero' hN]
        simp
        positivity
      · have hjv : j.val ≠ 0 := (ZMod.val_ne_zero j).mpr hj0
        have hxNat : 0 < k * N + j.val := by omega
        have hxyNat : k * N + j.val ≤ (k + 1) * N := by
          have hjlt := j.val_lt
          rw [Nat.add_mul, one_mul]
          omega
        have hlenNat : (k + 1) * N - (k * N + j.val) ≤ N := by
          have hjlt := j.val_lt
          rw [Nat.add_mul, one_mul]
          omega
        have hkN : k * N ≤ k * N + j.val := Nat.le_add_right _ _
        have hx : (0 : ℝ) < (k * N + j.val : ℕ) := by exact_mod_cast hxNat
        have hxy : ((k * N + j.val : ℕ) : ℝ) ≤ ((k + 1) * N : ℕ) := by
          exact_mod_cast hxyNat
        have hlen : (((k + 1) * N : ℕ) : ℝ) - (k * N + j.val : ℕ) ≤ N := by
          rw [← Nat.cast_sub hxyNat]
          exact_mod_cast hlenNat
        have hkNreal : ((k * N : ℕ) : ℝ) ≤ (k * N + j.val : ℕ) := by
          exact_mod_cast hkN
        have hkpos : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk)
        have hNpos : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
        have hvar := norm_cpow_neg_one_sub_le hx hxy
        rw [norm_mul]
        calc
          ‖chi j‖ * ‖((k * N + j.val : ℕ) : ℂ) ^ (-(1 : ℂ)) -
              (((k + 1) * N : ℕ) : ℂ) ^ (-(1 : ℂ))‖ ≤
              1 * (((((k + 1) * N : ℕ) : ℝ) - (k * N + j.val : ℕ)) /
                ((k * N + j.val : ℕ) : ℝ) ^ 2) := by
            have hvar' :
                ‖((k * N + j.val : ℕ) : ℂ) ^ (-(1 : ℂ)) -
                  (((k + 1) * N : ℕ) : ℂ) ^ (-(1 : ℂ))‖ ≤
                    ((((k + 1) * N : ℕ) : ℝ) - (k * N + j.val : ℕ)) /
                      ((k * N + j.val : ℕ) : ℝ) ^ 2 := by
              rw [show (-(1 : ℂ)) = ((-1 : ℝ) : ℂ) by norm_num]
              simpa only [Complex.ofReal_natCast] using hvar
            exact mul_le_mul (chi.norm_le_one j) hvar'
              (by positivity) (by positivity)
          _ ≤ (N : ℝ) / ((k * N + j.val : ℕ) : ℝ) ^ 2 := by
            simpa using div_le_div_of_nonneg_right hlen (sq_nonneg _)
          _ ≤ (N : ℝ) / ((k * N : ℕ) : ℝ) ^ 2 := by
            have hkNposNat : 0 < k * N := Nat.mul_pos (lt_of_lt_of_le Nat.zero_lt_one hk) (NeZero.pos N)
            have hdenpos : 0 < (((k * N : ℕ) : ℝ) ^ 2) := by
              exact pow_pos (by exact_mod_cast hkNposNat) 2
            have hsq : (((k * N : ℕ) : ℝ) ^ 2) ≤
                (((k * N + j.val : ℕ) : ℝ) ^ 2) := by
              nlinarith [show (0 : ℝ) ≤ (k * N : ℕ) by positivity]
            exact div_le_div_of_nonneg_left hNpos.le hdenpos hsq
          _ = (((k : ℝ) ^ 2) * (N : ℝ))⁻¹ := by
            norm_num [Nat.cast_mul]
            field_simp
    _ = ((k : ℝ) ^ 2)⁻¹ := by
      simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
      have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hk))
      have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne N
      field_simp

end BombieriVinogradov.SiegelWalfisz
