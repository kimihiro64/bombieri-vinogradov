import BombieriVinogradov.Proof.SiegelWalfisz.Siegel.ZeroExclusion.CpowVariation
import BombieriVinogradov.Proof.SiegelWalfisz.Siegel.ZeroExclusion.ModulusFactor
import BombieriVinogradov.Proof.SiegelWalfisz.Siegel.ZeroExclusion.TailFactor
import BombieriVinogradov.Proof.SiegelWalfisz.SiegelProduct.Cauchy.CharacterBlocks

/-!
# Positive-index complete-block bound near one

This module bounds each positive-index character block by a fixed summable
power, uniformly in the character modulus.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem norm_characterLBlock_tail_near_one_le {N : ℕ} [NeZero N]
    (chi : DirichletCharacter ℂ N) (hchi : Ne chi 1)
    {k : ℕ} (hk : 1 ≤ k) {s : ℂ}
    (hre : 1 - 1 / (8 * (1 + Real.log N)) ≤ s.re)
    (hseven : 7 / 8 ≤ s.re) (hnorm : ‖s‖ ≤ 2) :
    ‖characterLBlock chi k s‖ ≤
      2 * Real.exp (1 / 8 : ℝ) * (k : ℝ) ^ (-15 / 8 : ℝ) := by
  have hNOne : Ne N 1 := by
    intro h
    subst N
    exact hchi (Subsingleton.elim _ _)
  have hN : 0 < N := NeZero.pos N
  have hkpos : 0 < k := Nat.zero_lt_of_lt hk
  rw [characterLBlock_recenter chi hchi]
  calc
    ‖∑ j : ZMod N, chi j *
        (((k * N + j.val : ℕ) : ℂ) ^ (-s) - (((k + 1) * N : ℕ) : ℂ) ^ (-s))‖ ≤
        ∑ j : ZMod N, ‖chi j *
          (((k * N + j.val : ℕ) : ℂ) ^ (-s) -
            (((k + 1) * N : ℕ) : ℂ) ^ (-s))‖ := norm_sum_le _ _
    _ ≤ ∑ _j : ZMod N,
        2 * (N : ℝ) * (((k : ℝ) * (N : ℝ)) ^ (-s.re - 1)) := by
      apply Finset.sum_le_sum
      intro j hj
      by_cases hj0 : j = 0
      · subst j
        rw [chi.map_zero' hNOne]
        simp
        positivity
      · have hjv : Ne j.val 0 := (ZMod.val_ne_zero j).mpr hj0
        have hxNat : 1 ≤ k * N + j.val := by omega
        have hxyNat : k * N + j.val ≤ (k + 1) * N := by
          have hjlt := j.val_lt
          rw [Nat.add_mul, one_mul]
          omega
        have hlenNat : (k + 1) * N - (k * N + j.val) ≤ N := by
          have hjlt := j.val_lt
          rw [Nat.add_mul, one_mul]
          omega
        have hkNNat : k * N ≤ k * N + j.val := Nat.le_add_right _ _
        have hx : (1 : ℝ) ≤ (k * N + j.val : ℕ) := by exact_mod_cast hxNat
        have hxy : ((k * N + j.val : ℕ) : ℝ) ≤ ((k + 1) * N : ℕ) := by
          exact_mod_cast hxyNat
        have hlen : (((k + 1) * N : ℕ) : ℝ) - (k * N + j.val : ℕ) ≤ N := by
          rw [← Nat.cast_sub hxyNat]
          exact_mod_cast hlenNat
        have hkNcast : ((k * N : ℕ) : ℝ) ≤ (k * N + j.val : ℕ) := by
          exact_mod_cast hkNNat
        have hkN : ((k : ℝ) * (N : ℝ)) ≤ (k * N + j.val : ℕ) := by
          simpa [Nat.cast_mul] using hkNcast
        have hkNpos : (0 : ℝ) < (k : ℝ) * (N : ℝ) := by positivity
        have hpower : ((k * N + j.val : ℕ) : ℝ) ^ (-s.re - 1) ≤
            ((k : ℝ) * (N : ℝ)) ^ (-s.re - 1) :=
          Real.rpow_le_rpow_of_nonpos hkNpos hkN (by linarith)
        have hvar := norm_cpow_neg_sub_le_re hx hxy (by linarith : 0 ≤ s.re)
        rw [norm_mul]
        calc
          ‖chi j‖ * ‖((k * N + j.val : ℕ) : ℂ) ^ (-s) -
              (((k + 1) * N : ℕ) : ℂ) ^ (-s)‖ ≤
              1 * (‖s‖ *
                ((((k + 1) * N : ℕ) : ℝ) - (k * N + j.val : ℕ)) *
                  ((k * N + j.val : ℕ) : ℝ) ^ (-s.re - 1)) :=
            mul_le_mul (chi.norm_le_one j) hvar (by positivity) (by positivity)
          _ ≤ 2 * (N : ℝ) * ((k * N + j.val : ℕ) : ℝ) ^ (-s.re - 1) := by
            have hlenNonneg : 0 ≤
                (((k + 1) * N : ℕ) : ℝ) - (k * N + j.val : ℕ) :=
              sub_nonneg.mpr hxy
            have hcoefficient := mul_le_mul hnorm hlen hlenNonneg (by norm_num)
            have hscaled := mul_le_mul_of_nonneg_right hcoefficient
              (Real.rpow_nonneg (Nat.cast_nonneg (k * N + j.val)) (-s.re - 1))
            simpa [one_mul, mul_assoc] using hscaled
          _ ≤ 2 * (N : ℝ) * (((k : ℝ) * (N : ℝ)) ^ (-s.re - 1)) :=
            mul_le_mul_of_nonneg_left hpower (by positivity)
    _ = 2 * (N : ℝ) ^ 2 * (((k : ℝ) * (N : ℝ)) ^ (-s.re - 1)) := by
      simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
      ring
    _ = 2 * ((N : ℝ) ^ (1 - s.re) * (k : ℝ) ^ (-s.re - 1)) := by
      rw [show 2 * (N : ℝ) ^ 2 * (((k : ℝ) * (N : ℝ)) ^ (-s.re - 1)) =
        2 * ((N : ℝ) ^ 2 * (((k : ℝ) * (N : ℝ)) ^ (-s.re - 1))) by ring,
        modulus_block_rpow_factorization hN hkpos s.re]
    _ ≤ 2 * (Real.exp (1 / 8 : ℝ) * (k : ℝ) ^ (-15 / 8 : ℝ)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul (modulus_rpow_one_sub_re_le hN hre)
          (block_rpow_le_fixed hk hseven)
          (Real.rpow_nonneg (by positivity) _) (Real.exp_nonneg _)) (by norm_num)
    _ = 2 * Real.exp (1 / 8 : ℝ) * (k : ℝ) ^ (-15 / 8 : ℝ) := by ring

end BombieriVinogradov.SiegelWalfisz
