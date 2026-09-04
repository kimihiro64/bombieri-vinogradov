import Mathlib.Data.Complex.Basic
import Mathlib.Data.Int.Cast.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.NumberTheory.MulChar.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.Ring

/-!
# Difference from the primitive character at natural arguments

Changing level preserves values at coprime arguments and sets the ambient
value to zero elsewhere.
-/
set_option autoImplicit false

namespace BombieriVinogradov.DirichletCharacter

theorem natCast_sub_primitiveCharacter_eq {N : Nat}
    (chi : _root_.DirichletCharacter Complex N) (n : Nat) :
    chi (n : ZMod N) - chi.primitiveCharacter (n : ZMod chi.conductor) =
      if Nat.Coprime n N then 0
      else -chi.primitiveCharacter (n : ZMod chi.conductor) := by
  by_cases h : Nat.Coprime n N
  case pos =>
    rw [if_pos h]
    have hInt := chi.primitiveCharacter_apply_of_isCoprime
      (Nat.isCoprime_iff_coprime.mpr h)
    have hNat :
        chi.primitiveCharacter (n : ZMod chi.conductor) = chi (n : ZMod N) := by
      simpa only [Int.cast_natCast] using hInt
    rw [hNat]
    ring
  case neg =>
    rw [if_neg h]
    have hZero : chi (n : ZMod N) = 0 :=
      chi.map_nonunit (fun hUnit => h ((ZMod.isUnit_iff_coprime n N).mp hUnit))
    rw [hZero]
    ring

end BombieriVinogradov.DirichletCharacter
