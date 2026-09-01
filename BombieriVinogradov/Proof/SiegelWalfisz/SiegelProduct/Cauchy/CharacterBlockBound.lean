import BombieriVinogradov.Proof.SiegelWalfisz.SiegelProduct.Cauchy.CharacterBlocks
import BombieriVinogradov.Proof.SiegelWalfisz.SiegelProduct.Cauchy.CpowVariation

/-!
# Summable majorant for grouped character blocks

This module owns the uniform norm estimate for one complete residue block on
the fixed analytic domain.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

/-- The character-independent majorant for the `k`th complete residue block. -/
noncomputable def characterLBlockMajorant (N k : ℕ) : ℝ :=
  (15 / 4 : ℝ) * (N : ℝ) ^ 2 * ((k + 1 : ℕ) : ℝ) ^ (-5 / 4 : ℝ)

theorem norm_characterLBlock_le {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (k : ℕ) {s : ℂ}
    (hs : s ∈ siegelAnalyticDomain) :
    ‖characterLBlock χ k s‖ ≤ characterLBlockMajorant N k := by
  have hN : N ≠ 1 := by
    intro h
    subst N
    exact hχ (Subsingleton.elim _ _)
  rw [characterLBlock_recenter χ hχ]
  calc
    ‖∑ j : ZMod N, χ j *
        (((k * N + j.val : ℕ) : ℂ) ^ (-s) - (((k + 1) * N : ℕ) : ℂ) ^ (-s))‖
        ≤ ∑ j : ZMod N, ‖χ j *
          (((k * N + j.val : ℕ) : ℂ) ^ (-s) - (((k + 1) * N : ℕ) : ℂ) ^ (-s))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _j : ZMod N,
        (15 / 4 : ℝ) * (N : ℝ) * ((k + 1 : ℕ) : ℝ) ^ (-5 / 4 : ℝ) := by
      apply Finset.sum_le_sum
      intro j hj
      by_cases hj0 : j = 0
      · subst j
        rw [χ.map_zero' hN]
        simp only [zero_mul, norm_zero]
        positivity
      · have hjv : j.val ≠ 0 := (ZMod.val_ne_zero j).mpr hj0
        have hxoneNat : 1 ≤ k * N + j.val := by omega
        have hxyNat : k * N + j.val ≤ (k + 1) * N := by
          have hjlt := j.val_lt
          rw [Nat.add_mul, one_mul]
          omega
        have hlenNat : (k + 1) * N - (k * N + j.val) ≤ N := by
          have hjlt := j.val_lt
          rw [Nat.add_mul, one_mul]
          omega
        have hxkNat : k + 1 ≤ k * N + j.val := by
          have hNp := NeZero.pos N
          have hk : k ≤ k * N := by
            simpa using Nat.mul_le_mul_left k hNp
          omega
        have hxone : (1 : ℝ) ≤ (k * N + j.val : ℕ) := by exact_mod_cast hxoneNat
        have hxy : ((k * N + j.val : ℕ) : ℝ) ≤ ((k + 1) * N : ℕ) := by
          exact_mod_cast hxyNat
        have hlen : (((k + 1) * N : ℕ) : ℝ) - (k * N + j.val : ℕ) ≤ N := by
          rw [← Nat.cast_sub hxyNat]
          exact_mod_cast hlenNat
        have hxk : (((k + 1 : ℕ) : ℝ)) ≤ (k * N + j.val : ℕ) := by
          exact_mod_cast hxkNat
        have hpow : ((k * N + j.val : ℕ) : ℝ) ^ (-5 / 4 : ℝ) ≤
            ((k + 1 : ℕ) : ℝ) ^ (-5 / 4 : ℝ) := by
          exact Real.rpow_le_rpow_of_nonpos (by positivity) hxk (by norm_num)
        have hvar := norm_cpow_neg_sub_le hxone hxy
          (le_of_lt (siegelAnalyticDomain_re_lower hs))
          (le_of_lt (siegelAnalyticDomain_norm_upper hs))
        rw [norm_mul]
        calc
          ‖χ j‖ * ‖((k * N + j.val : ℕ) : ℂ) ^ (-s) -
              (((k + 1) * N : ℕ) : ℂ) ^ (-s)‖
              ≤ ‖χ j‖ * ((15 / 4 : ℝ) *
                ((((k + 1) * N : ℕ) : ℝ) - (k * N + j.val : ℕ)) *
                  ((k * N + j.val : ℕ) : ℝ) ^ (-5 / 4 : ℝ)) :=
            mul_le_mul_of_nonneg_left hvar (norm_nonneg _)
          _ ≤ 1 * ((15 / 4 : ℝ) *
                ((((k + 1) * N : ℕ) : ℝ) - (k * N + j.val : ℕ)) *
                  ((k * N + j.val : ℕ) : ℝ) ^ (-5 / 4 : ℝ)) := by
            gcongr
            exact χ.norm_le_one j
          _ = (15 / 4 : ℝ) *
                ((((k + 1) * N : ℕ) : ℝ) - (k * N + j.val : ℕ)) *
                  ((k * N + j.val : ℕ) : ℝ) ^ (-5 / 4 : ℝ) := by ring
          _ ≤ (15 / 4 : ℝ) * (N : ℝ) *
                ((k * N + j.val : ℕ) : ℝ) ^ (-5 / 4 : ℝ) := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hlen (by norm_num)) (Real.rpow_nonneg (by positivity) _)
          _ ≤ (15 / 4 : ℝ) * (N : ℝ) * ((k + 1 : ℕ) : ℝ) ^ (-5 / 4 : ℝ) := by
            exact mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = characterLBlockMajorant N k := by
      simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
      rw [characterLBlockMajorant]
      ring

end BombieriVinogradov.SiegelWalfisz
