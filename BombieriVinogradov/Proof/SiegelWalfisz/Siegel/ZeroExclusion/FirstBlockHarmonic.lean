import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Harmonic bound for one complete residue system

This module bounds the reciprocal values of `ZMod` representatives by a
harmonic sum. It is independent of Dirichlet L-functions.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem sum_zmod_val_inv_le_harmonic (N : ℕ) [NeZero N] :
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

end BombieriVinogradov.SiegelWalfisz
