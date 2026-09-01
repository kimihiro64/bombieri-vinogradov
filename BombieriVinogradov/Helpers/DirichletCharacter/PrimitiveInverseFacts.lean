import Mathlib.NumberTheory.LSeries.DirichletContinuation

/-!
# Inverse-character facts

This module collects the reusable facts that inversion preserves nonprincipality and
primitivity for complex Dirichlet characters.
-/

set_option autoImplicit false

namespace BombieriVinogradov

theorem DirichletCharacter.inv_ne_one_of_ne_one
    {N : Nat} {chi : DirichletCharacter Complex N}
    (hchi : chi ≠ 1) : chi⁻¹ ≠ 1 := by
  intro hInverse
  apply hchi
  calc
    chi = (chi⁻¹)⁻¹ := by simp
    _ = (1 : DirichletCharacter Complex N)⁻¹ := congrArg Inv.inv hInverse
    _ = 1 := by simp

theorem DirichletCharacter.IsPrimitive.inv
    {N : Nat} {chi : DirichletCharacter Complex N}
    (hPrimitive : DirichletCharacter.IsPrimitive chi) :
    DirichletCharacter.IsPrimitive chi⁻¹ := by
  rw [DirichletCharacter.IsPrimitive,
    DirichletCharacter.conductor_inv, hPrimitive]

end BombieriVinogradov
