import BombieriVinogradov.Helpers.DirichletCharacter.ConductorFacts
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedZeroStrip
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.ComplexZeroCoreInequality
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.ComplexZeroOptimization
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Primitive complex-character zero gap

This module optimizes the core logarithmic-derivative inequality at a
multiplicity-indexed zero.  It is the primitive complex-character part of
Strombergsson's Theorem 11.4, before transfer from a general character to its
primitive character.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem exists_primitive_complexZero_gap :
    exists c : Real, 0 < c ∧
      forall {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N},
        chi ≠ 1 -> DirichletCharacter.IsPrimitive chi -> chi ^ 2 ≠ 1 ->
          forall p : SymmetricCompletedZeroIndex chi,
            c / (Real.log N +
              Real.log (|(Complex.Hadamard.divisorZeroIndex₀_val p).im| + 2)) ≤
              1 - (Complex.Hadamard.divisorZeroIndex₀_val p).re := by
  obtain ⟨K0, hK0Pos, hCore⟩ := exists_complexZero_core_inequality
  let K := K0 + (Real.log 3)⁻¹
  let c := (14 * K)⁻¹
  have hLogThree : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hKPos : 0 < K := add_pos hK0Pos (inv_pos.mpr hLogThree)
  have hcPos : 0 < c := inv_pos.mpr (mul_pos (by norm_num) hKPos)
  refine Exists.intro c (And.intro hcPos ?_)
  intro N _hN chi hchi hPrimitive hchiSquare p
  let L := Real.log N +
    Real.log (|(Complex.Hadamard.divisorZeroIndex₀_val p).im| + 2)
  have hNLower :=
    BombieriVinogradov.DirichletCharacter.three_le_level_of_ne_one chi hchi
  have hLogNLower : Real.log 3 ≤ Real.log N :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hNLower)
  have hHeightLogNonneg :
      0 ≤ Real.log (|(Complex.Hadamard.divisorZeroIndex₀_val p).im| + 2) := by
    apply Real.log_nonneg
    linarith [abs_nonneg (Complex.Hadamard.divisorZeroIndex₀_val p).im]
  have hLLower : Real.log 3 ≤ L := by
    dsimp [L]
    linarith
  have hLPos : 0 < L := hLogThree.trans_le hLLower
  have hInvLogNonneg : 0 ≤ (Real.log 3)⁻¹ := (inv_pos.mpr hLogThree).le
  have hInvLogL : 1 ≤ (Real.log 3)⁻¹ * L := by
    have hScaled := mul_le_mul_of_nonneg_left hLLower hInvLogNonneg
    have hCancel : (Real.log 3)⁻¹ * Real.log 3 = 1 := by
      field_simp
    rw [hCancel] at hScaled
    exact hScaled
  have hKL : 1 ≤ K * L := by
    have hK0LNonneg : 0 ≤ K0 * L := mul_nonneg hK0Pos.le hLPos.le
    dsimp [K]
    nlinarith
  have hStrip :=
    symmetricCompletedLFunction_divisorZeroIndex₀_re_mem_Ioo hchi hPrimitive p
  have hCoreK : forall sigma : Real, 1 < sigma -> sigma ≤ 2 ->
      4 * (sigma - (Complex.Hadamard.divisorZeroIndex₀_val p).re)⁻¹ ≤
        3 * (sigma - 1)⁻¹ + K * L := by
    intro sigma hsigma hsigmaUpper
    have hCore0 := hCore hchi hPrimitive hchiSquare p hsigma hsigmaUpper rfl
    change 4 * (sigma -
        (Complex.Hadamard.divisorZeroIndex₀_val p).re)⁻¹ ≤
      3 * (sigma - 1)⁻¹ + K0 * L at hCore0
    have hLNonneg : 0 ≤ L := hLPos.le
    have hCoefficient : K0 * L ≤ K * L := by
      apply mul_le_mul_of_nonneg_right
      · dsimp [K]
        exact le_add_of_nonneg_right hInvLogNonneg
      · exact hLNonneg
    exact hCore0.trans (by
      simpa [add_comm] using
        add_le_add_left hCoefficient (3 * (sigma - 1)⁻¹))
  have hGap := core_inequality_implies_gap hStrip.2 hKPos hLPos hKL hCoreK
  have hIdentity : c / L = (14 * K * L)⁻¹ := by
    dsimp [c]
    field_simp
  rw [hIdentity]
  exact hGap

end BombieriVinogradov.SiegelWalfisz
