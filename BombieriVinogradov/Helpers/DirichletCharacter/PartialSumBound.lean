import BombieriVinogradov.Helpers.DirichletCharacter.PartialSumIdentity
import Mathlib.Analysis.Complex.Basic
import Mathlib.NumberTheory.DirichletCharacter.Bounds

/-!
# Uniform Dirichlet-character partial-sum bound

This module owns the modulus bound for the exact `Icc 1 n` character prefix
used by Mathlib's L-series integral representation.
-/

set_option autoImplicit false

open Finset

namespace BombieriVinogradov

/-- Every nonprincipal character prefix over `Icc 1 n` has norm at most its modulus. -/
theorem norm_sum_character_Icc_le_modulus {N : ℕ} [NeZero N]
    (chi : DirichletCharacter ℂ N) (hchi : chi ≠ 1) (n : ℕ) :
    ‖(∑ k ∈ Icc 1 n, chi k)‖ ≤ (N : ℝ) := by
  have hN : N ≠ 1 := by
    intro h
    subst N
    exact hchi (Subsingleton.elim _ _)
  have hzero : chi 0 = 0 := chi.map_zero' hN
  have hIcc : (∑ k ∈ Icc 1 n, chi k) = ∑ k ∈ range (n + 1), chi k := by
    rw [Nat.range_succ_eq_Icc_zero]
    symm
    rw [← insert_Icc_add_one_left_eq_Icc n.zero_le, sum_insert (by simp)]
    simp [hzero]
  have hRange (m : ℕ) : ‖(∑ k ∈ range m, chi k)‖ ≤ (N : ℝ) := by
    rw [sum_character_range_eq_sum_mod chi hchi]
    calc
      ‖(∑ k ∈ range (m % N), chi k)‖ ≤ ∑ k ∈ range (m % N), ‖chi k‖ :=
        norm_sum_le _ _
      _ ≤ ∑ _k ∈ range (m % N), (1 : ℝ) := by
        exact Finset.sum_le_sum fun k _hk => chi.norm_le_one k
      _ = (m % N : ℕ) := by simp
      _ ≤ (N : ℝ) := by
        exact_mod_cast (Nat.mod_lt m (NeZero.pos N)).le
  rw [hIcc]
  exact hRange (n + 1)

end BombieriVinogradov
