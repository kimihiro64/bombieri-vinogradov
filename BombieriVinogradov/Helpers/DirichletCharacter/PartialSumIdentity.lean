import BombieriVinogradov.Helpers.DirichletCharacter.CompletePeriod

/-!
# Dirichlet-character prefix reduction

This module owns the exact reduction of an arbitrary natural prefix of a
nonprincipal character to its final incomplete residue block.
-/

set_option autoImplicit false

open Finset

namespace BombieriVinogradov

/-- Every full modulus block cancels from a nonprincipal character prefix sum. -/
theorem sum_character_range_eq_sum_mod {N : ℕ} [NeZero N]
    (chi : DirichletCharacter ℂ N) (hchi : chi ≠ 1) (n : ℕ) :
    ∑ k ∈ range n, chi k = ∑ k ∈ range (n % N), chi k := by
  have hfull : ∀ q : ℕ, ∑ k ∈ range (q * N), chi k = 0 := by
    intro q
    induction q with
    | zero => simp
    | succ q ih =>
        rw [Nat.succ_mul, Finset.sum_range_add, ih, zero_add]
        simpa using sum_character_range_modulus_eq_zero chi hchi
  have hn : n = (n / N) * N + n % N := by
    simpa [Nat.mul_comm] using (Nat.div_add_mod n N).symm
  nth_rewrite 1 [hn]
  rw [Finset.sum_range_add, hfull, zero_add]
  exact Finset.sum_congr rfl fun k _hk => by simp

/-- The zero endpoint contributes nothing to a nonprincipal character sum. -/
theorem sum_character_Icc_zero_eq_one {N : ℕ} [NeZero N]
    (chi : DirichletCharacter ℂ N) (hchi : chi ≠ 1) (n : ℕ) :
    ∑ k ∈ Icc 0 n, chi k = ∑ k ∈ Icc 1 n, chi k := by
  have hN : N ≠ 1 := by
    intro h
    subst N
    exact hchi (Subsingleton.elim _ _)
  have hzero : chi 0 = 0 := chi.map_zero' hN
  rw [← insert_Icc_add_one_left_eq_Icc n.zero_le, sum_insert (by simp)]
  simp [hzero]

end BombieriVinogradov
