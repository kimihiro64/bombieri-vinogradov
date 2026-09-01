import Mathlib.Analysis.Complex.Basic
import Mathlib.NumberTheory.DirichletCharacter.Basic

/-!
# Conductor facts for nonprincipal characters

This module keeps primitive-character nonprincipality and the elementary
conductor bound available below every proof branch that needs them.
-/

set_option autoImplicit false

namespace BombieriVinogradov.DirichletCharacter

/-- Every nonprincipal complex Dirichlet character has level at least three. -/
theorem three_le_level_of_ne_one {N : Nat} [NeZero N]
    (chi : _root_.DirichletCharacter Complex N) (hchi : chi ≠ 1) : 3 ≤ N := by
  by_contra hN
  have hNle : N ≤ 2 := by omega
  interval_cases N
  · exact (NeZero.ne 0) rfl
  · exact hchi (Subsingleton.elim _ _)
  · apply hchi
    ext x
    have hx : x = 1 := Subsingleton.elim _ _
    subst x
    simp

theorem primitiveCharacter_ne_one_of_ne_one {N : Nat} [NeZero N]
    (chi : _root_.DirichletCharacter Complex N) (hchi : chi ≠ 1) :
    chi.primitiveCharacter ≠ 1 := by
  intro hprimitive
  apply hchi
  rw [← chi.changeLevel_primitiveCharacter, hprimitive]
  simp

theorem primitiveCharacter_pow_ne_one_of_pow_ne_one
    {N m : Nat} [NeZero N] (chi : _root_.DirichletCharacter Complex N)
    (hchi : chi ^ m ≠ 1) : chi.primitiveCharacter ^ m ≠ 1 := by
  intro hPrimitive
  apply hchi
  let lift : _root_.DirichletCharacter Complex chi.conductor →*
      _root_.DirichletCharacter Complex N :=
    _root_.DirichletCharacter.changeLevel (R := Complex)
      chi.conductor_dvd_level
  have hLift : lift chi.primitiveCharacter = chi :=
    chi.changeLevel_primitiveCharacter
  calc
    chi ^ m = (lift chi.primitiveCharacter) ^ m := by rw [hLift]
    _ = lift (chi.primitiveCharacter ^ m) := by
      rw [map_pow]
    _ = lift 1 := by
      rw [hPrimitive]
    _ = 1 := by
      rw [map_one]

theorem conductor_le_level {N : Nat} [NeZero N]
    (chi : _root_.DirichletCharacter Complex N) : chi.conductor ≤ N :=
  Nat.le_of_dvd (NeZero.pos N) chi.conductor_dvd_level

theorem three_le_conductor_of_ne_one {N : Nat} [NeZero N]
    (chi : _root_.DirichletCharacter Complex N) (hchi : chi ≠ 1) :
    3 ≤ chi.conductor := by
  let _ : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  exact three_le_level_of_ne_one chi.primitiveCharacter
    (primitiveCharacter_ne_one_of_ne_one chi hchi)

end BombieriVinogradov.DirichletCharacter
