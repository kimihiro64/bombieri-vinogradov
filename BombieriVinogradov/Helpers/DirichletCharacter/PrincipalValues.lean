import Mathlib.Data.Complex.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.NumberTheory.MulChar.Basic

/-!
# Principal character values at natural arguments

The principal character is exactly the coprimality indicator, including
the modulus-one convention.
-/
set_option autoImplicit false

namespace BombieriVinogradov.DirichletCharacter

theorem principal_natCast_eq_indicator (N n : Nat) :
    (1 : _root_.DirichletCharacter Complex N) (n : ZMod N) =
      if Nat.Coprime n N then 1 else 0 := by
  by_cases h : Nat.Coprime n N
  case pos =>
    rw [if_pos h]
    exact MulChar.one_apply ((ZMod.isUnit_iff_coprime n N).mpr h)
  case neg =>
    rw [if_neg h]
    exact (1 : _root_.DirichletCharacter Complex N).map_nonunit
      (fun hUnit => h ((ZMod.isUnit_iff_coprime n N).mp hUnit))

end BombieriVinogradov.DirichletCharacter
