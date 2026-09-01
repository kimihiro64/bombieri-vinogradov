import Mathlib.Analysis.Complex.Basic
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.NumberTheory.LegendreSymbol.ZModChar

/-!
# Primitive-character facts for Siegel's lower bound

This module proves nonprincipality at level at least three and for products at distinct levels.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

/-- The standard primitive quadratic character modulo four, with complex values. -/
noncomputable def quadraticCharacterFour : DirichletCharacter ℂ 4 :=
  ZMod.χ₄.ringHomComp (Int.castRingHom ℂ)

theorem quadraticCharacterFour_sq : quadraticCharacterFour ^ 2 = 1 :=
  (ZMod.isQuadratic_χ₄.comp (Int.castRingHom ℂ)).sq_eq_one

theorem quadraticCharacterFour_ne_one : quadraticCharacterFour ≠ 1 := by
  rw [quadraticCharacterFour, MulChar.ringHomComp_ne_one_iff Int.cast_injective]
  intro hone
  have hvalue := congrArg (fun chi : MulChar (ZMod 4) ℤ ↦ chi (3 : ℕ)) hone
  have hthree : ZMod.χ₄ (3 : ℕ) = -1 :=
    ZMod.χ₄_nat_three_mod_four (by norm_num)
  rw [hthree] at hvalue
  have hunit : IsUnit (3 : ZMod 4) := by decide
  have honeValue : (1 : MulChar (ZMod 4) ℤ) ((3 : ℕ) : ZMod 4) = 1 :=
    MulChar.one_apply hunit
  rw [honeValue] at hvalue
  norm_num at hvalue

/-- Every nonprincipal complex Dirichlet character has level at least three. -/
theorem three_le_level_of_ne_one {N : ℕ} [NeZero N]
    (chi : DirichletCharacter ℂ N) (hchi : chi ≠ 1) : 3 ≤ N := by
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

theorem primitive_ne_one_of_three_le {N : ℕ} [NeZero N]
    (chi : DirichletCharacter ℂ N) (hchi : DirichletCharacter.IsPrimitive chi)
    (hN : 3 ≤ N) : chi ≠ 1 := by
  intro hone
  subst chi
  rw [DirichletCharacter.IsPrimitive,
    DirichletCharacter.conductor_one] at hchi
  omega

theorem primitiveCharacter_ne_one {N : ℕ} [NeZero N]
    (chi : DirichletCharacter ℂ N) (hchi : chi ≠ 1) :
    chi.primitiveCharacter ≠ 1 := by
  intro hprimitive
  apply hchi
  rw [← chi.changeLevel_primitiveCharacter, hprimitive]
  simp

theorem primitiveCharacter_sq_eq_one {N : ℕ} [NeZero N]
    (chi : DirichletCharacter ℂ N) (hchi : chi ^ 2 = 1) :
    chi.primitiveCharacter ^ 2 = 1 := by
  apply DirichletCharacter.changeLevel_injective chi.conductor_dvd_level
  rw [map_pow, chi.changeLevel_primitiveCharacter, hchi, map_one]

theorem three_le_conductor_of_ne_one {N : ℕ} [NeZero N]
    (chi : DirichletCharacter ℂ N) (hchi : chi ≠ 1) :
    3 ≤ chi.conductor := by
  let _ : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  exact three_le_level_of_ne_one chi.primitiveCharacter
    (primitiveCharacter_ne_one chi hchi)

theorem quadraticCharacterFour_isPrimitive :
    DirichletCharacter.IsPrimitive quadraticCharacterFour := by
  rw [DirichletCharacter.IsPrimitive]
  have hlower := three_le_conductor_of_ne_one quadraticCharacterFour
    quadraticCharacterFour_ne_one
  have hdvd := quadraticCharacterFour.conductor_dvd_level
  have hupper : quadraticCharacterFour.conductor ≤ 4 :=
    Nat.le_of_dvd (by norm_num) hdvd
  interval_cases quadraticCharacterFour.conductor
  · norm_num at hdvd
  · rfl

theorem crossLevelMul_sq_eq_one {N M : ℕ}
    [NeZero N] [NeZero M] [NeZero (N.lcm M)]
    (chi : DirichletCharacter ℂ N) (psi : DirichletCharacter ℂ M)
    (hchiSquare : chi ^ 2 = 1) (hpsiSquare : psi ^ 2 = 1) :
    DirichletCharacter.mul chi psi ^ 2 = 1 := by
  change (DirichletCharacter.changeLevel (Nat.dvd_lcm_left N M) chi *
      DirichletCharacter.changeLevel (Nat.dvd_lcm_right N M) psi) ^ 2 = 1
  rw [mul_pow, ← map_pow, hchiSquare, map_one, ← map_pow, hpsiSquare, map_one, one_mul]

theorem crossLevelMul_ne_one_of_primitive_of_ne {N M : ℕ}
    [NeZero N] [NeZero M] [NeZero (N.lcm M)]
    (chi : DirichletCharacter ℂ N) (psi : DirichletCharacter ℂ M)
    (hchi : DirichletCharacter.IsPrimitive chi)
    (hpsi : DirichletCharacter.IsPrimitive psi) (hNM : N ≠ M) :
    DirichletCharacter.mul chi psi ≠ 1 := by
  intro hmul
  change DirichletCharacter.changeLevel (Nat.dvd_lcm_left N M) chi *
      DirichletCharacter.changeLevel (Nat.dvd_lcm_right N M) psi = 1 at hmul
  have hinv : DirichletCharacter.changeLevel (Nat.dvd_lcm_left N M) chi =
      (DirichletCharacter.changeLevel (Nat.dvd_lcm_right N M) psi)⁻¹ :=
    eq_inv_of_mul_eq_one_left hmul
  have hconductor := congrArg DirichletCharacter.conductor hinv
  rw [DirichletCharacter.conductor_changeLevel,
    DirichletCharacter.conductor_inv,
    DirichletCharacter.conductor_changeLevel,
    hchi, hpsi] at hconductor
  exact hNM hconductor

end BombieriVinogradov.SiegelWalfisz
