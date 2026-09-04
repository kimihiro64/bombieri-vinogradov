import BombieriVinogradov.Helpers.DirichletCharacter.PrincipalValues
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.DirichletCharacter.Basic

/-!
# Exact finite principal-character correction

The difference from the principal twist is precisely the sum over
indices not coprime to the ambient modulus.
-/
set_option autoImplicit false

namespace BombieriVinogradov.DirichletCharacter

theorem sum_sub_principal_eq_sum_filter (N : Nat)
    (s : Finset Nat) (f : Nat -> Complex) :
    Finset.sum s f - Finset.sum s (fun n =>
      f n * (1 : _root_.DirichletCharacter Complex N) (n : ZMod N)) =
      Finset.sum (s.filter (fun n => Not (Nat.Coprime n N))) f := by
  rw [<- Finset.sum_sub_distrib, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n _hn
  rw [principal_natCast_eq_indicator]
  by_cases h : Nat.Coprime n N
  case pos =>
    have hNot : Not (Not (Nat.Coprime n N)) := fun hBad => hBad h
    rw [if_pos h, if_neg hNot, mul_one, sub_self]
  case neg =>
    rw [if_neg h, if_pos h, mul_zero, sub_zero]

end BombieriVinogradov.DirichletCharacter
