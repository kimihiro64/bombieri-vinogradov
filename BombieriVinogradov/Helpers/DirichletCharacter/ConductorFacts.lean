import Mathlib.Analysis.Complex.Basic
import Mathlib.NumberTheory.DirichletCharacter.Basic

/-!
# Conductor facts for nonprincipal characters

This module keeps primitive-character nonprincipality and the elementary
conductor bound available below every proof branch that needs them.
-/

set_option autoImplicit false

namespace BombieriVinogradov.DirichletCharacter

theorem primitiveCharacter_ne_one_of_ne_one {N : Nat} [NeZero N]
    (chi : _root_.DirichletCharacter Complex N) (hchi : chi ≠ 1) :
    chi.primitiveCharacter ≠ 1 := by
  intro hprimitive
  apply hchi
  rw [← chi.changeLevel_primitiveCharacter, hprimitive]
  simp

theorem conductor_le_level {N : Nat} [NeZero N]
    (chi : _root_.DirichletCharacter Complex N) : chi.conductor ≤ N :=
  Nat.le_of_dvd (NeZero.pos N) chi.conductor_dvd_level

end BombieriVinogradov.DirichletCharacter
