import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.NumberTheory.Divisors
import Mathlib.Tactic

/-!
# Finite hyperbola reindexing

This module isolates the exact finite bijection between divisor-antidiagonal
sums and the hyperbolic region used by Vaughan's Type I estimates.
-/

set_option autoImplicit false

noncomputable section

open Finset
open scoped BigOperators

namespace BombieriVinogradov.VaughanMeanValue

theorem sum_divisorsAntidiagonal_Icc_eq_hyperbola
    {A : Type*} [AddCommMonoid A] (F : Nat -> Nat -> A) (y : Nat) :
    ∑ n ∈ Icc 1 y, ∑ pair ∈ Nat.divisorsAntidiagonal n,
        F pair.1 pair.2 =
      ∑ m ∈ Icc 1 y, ∑ k ∈ Icc 1 (y / m), F m k := by
  classical
  rw [Finset.sum_sigma', Finset.sum_sigma']
  apply Finset.sum_bij
    (fun x _ => Sigma.mk x.2.1 x.2.2)
  · intro x hx
    rcases Finset.mem_sigma.mp hx with ⟨hn, hp⟩
    rcases Nat.mem_divisorsAntidiagonal.mp hp with ⟨hprod, hn0⟩
    have hm0 : Ne x.2.1 0 := Nat.left_ne_zero_of_mem_divisorsAntidiagonal hp
    have hk0 : Ne x.2.2 0 := Nat.right_ne_zero_of_mem_divisorsAntidiagonal hp
    apply Finset.mem_sigma.mpr
    constructor
    · exact Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr hm0, by
        calc
          x.2.1 <= x.2.1 * x.2.2 :=
            Nat.le_mul_of_pos_right x.2.1 (Nat.pos_of_ne_zero hk0)
          _ = x.1 := hprod
          _ <= y := (Finset.mem_Icc.mp hn).2⟩
    · apply Finset.mem_Icc.mpr
      constructor
      · exact Nat.one_le_iff_ne_zero.mpr hk0
      · apply (Nat.le_div_iff_mul_le (Nat.pos_of_ne_zero hm0)).mpr
        simpa [Nat.mul_comm, hprod] using (Finset.mem_Icc.mp hn).2
  · intro x hx z hz heq
    rcases x with ⟨n, ⟨m, k⟩⟩
    rcases z with ⟨n', ⟨m', k'⟩⟩
    simp only [Sigma.mk.injEq] at heq
    rcases heq with ⟨rfl, rfl⟩
    have hxprod := (Nat.mem_divisorsAntidiagonal.mp
      (Finset.mem_sigma.mp hx).2).1
    have hzprod := (Nat.mem_divisorsAntidiagonal.mp
      (Finset.mem_sigma.mp hz).2).1
    have hnn : n = n' := hxprod.symm.trans hzprod
    cases hnn
    rfl
  · intro z hz
    rcases z with ⟨m, k⟩
    rcases Finset.mem_sigma.mp hz with ⟨hm, hk⟩
    have hmpos : 0 < m := (Finset.mem_Icc.mp hm).1
    have hkpos : 0 < k := (Finset.mem_Icc.mp hk).1
    have hprod : m * k <= y :=
      (by
        have := (Nat.le_div_iff_mul_le hmpos).mp (Finset.mem_Icc.mp hk).2
        simpa [Nat.mul_comm] using this)
    refine ⟨Sigma.mk (m * k) (m, k), ?_, ?_⟩
    · apply Finset.mem_sigma.mpr
      constructor
      · exact Finset.mem_Icc.mpr ⟨Nat.mul_pos hmpos hkpos, hprod⟩
      · exact Nat.mem_divisorsAntidiagonal.mpr ⟨rfl,
          (Nat.mul_pos hmpos hkpos).ne'⟩
    · rfl
  · intro x hx
    rfl

end BombieriVinogradov.VaughanMeanValue
