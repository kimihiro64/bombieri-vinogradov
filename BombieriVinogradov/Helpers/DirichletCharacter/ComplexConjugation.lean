import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.NumberTheory.LSeries.Basic
import Mathlib.NumberTheory.MulChar.Lemmas

/-!
# Complex conjugation for Dirichlet characters and L-series

This module proves the coefficient-level and naive-series conjugation identities needed
to transfer analytic continuation from a character to its inverse.
-/

set_option autoImplicit false

open scoped ComplexConjugate

namespace BombieriVinogradov

theorem DirichletCharacter.conj_apply_eq_inv_apply
    {N : Nat} (chi : DirichletCharacter Complex N) (a : ZMod N) :
    conj (chi a) = chi⁻¹ a := by
  simpa [RCLike.star_def] using MulChar.star_apply' chi a

theorem DirichletCharacter.Even.inv
    {N : Nat} {chi : DirichletCharacter Complex N}
    (hEven : DirichletCharacter.Even chi) :
    DirichletCharacter.Even chi⁻¹ := by
  rw [DirichletCharacter.Even, MulChar.inv_apply_eq_inv', hEven]
  simp

theorem DirichletCharacter.Odd.inv
    {N : Nat} {chi : DirichletCharacter Complex N}
    (hOdd : DirichletCharacter.Odd chi) :
    DirichletCharacter.Odd chi⁻¹ := by
  rw [DirichletCharacter.Odd, MulChar.inv_apply_eq_inv', hOdd]
  simp

theorem Complex.conj_natCast_cpow_conj
    (n : Nat) (s : Complex) :
    conj ((n : Complex) ^ conj s) = (n : Complex) ^ s := by
  have hArg : Complex.arg (n : Complex) ≠ Real.pi := by
    rw [Complex.natCast_arg]
    exact Real.pi_ne_zero.symm
  simpa using congrArg conj (Complex.cpow_conj (n : Complex) s hArg)

theorem DirichletCharacter.conj_LSeries_conj_eq_inv_LSeries
    {N : Nat} (chi : DirichletCharacter Complex N) (s : Complex) :
    conj (LSeries (chi ·) (conj s)) =
      LSeries (chi⁻¹ ·) s := by
  rw [LSeries, LSeries, RCLike.conj_tsum]
  apply tsum_congr
  intro n
  by_cases hn : n = 0
  · subst n
    simp
  · rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn]
    rw [map_div₀ (starRingEnd Complex),
      DirichletCharacter.conj_apply_eq_inv_apply,
      Complex.conj_natCast_cpow_conj]

end BombieriVinogradov
