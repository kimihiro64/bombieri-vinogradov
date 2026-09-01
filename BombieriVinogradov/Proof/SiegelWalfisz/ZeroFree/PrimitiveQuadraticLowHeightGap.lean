import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.QuadraticLowHeightOptimization
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.QuadraticNonrealZeroCoreInequality
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Low-height nonreal zero gap for a primitive quadratic character

This module packages equation (410) and its optimization with uniform absolute
height and horizontal-gap constants.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem exists_primitive_quadratic_lowHeight_nonreal_gap :
    exists cHeight cGap : Real, 0 < cHeight ∧ 0 < cGap ∧
      forall {N : Nat} [NeZero N], 3 ≤ N ->
        forall {chi : DirichletCharacter Complex N},
          chi ≠ 1 -> DirichletCharacter.IsPrimitive chi -> chi ^ 2 = 1 ->
            forall p : SymmetricCompletedZeroIndex chi,
              0 < (Complex.Hadamard.divisorZeroIndex₀_val p).im ->
              (Complex.Hadamard.divisorZeroIndex₀_val p).im <
                cHeight / Real.log N ->
                cGap / Real.log N ≤
                  1 - (Complex.Hadamard.divisorZeroIndex₀_val p).re := by
  obtain ⟨K0, hK0Pos, hCore⟩ :=
    exists_quadratic_nonrealZero_core_inequality
  let K := K0 + (Real.log 3)⁻¹
  let cHeight := (10 * K)⁻¹
  let cGap := (15 * K)⁻¹
  have hLogThree : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hKPos : 0 < K := add_pos hK0Pos (inv_pos.mpr hLogThree)
  have hHeightPos : 0 < cHeight :=
    inv_pos.mpr (mul_pos (by norm_num) hKPos)
  have hGapPos : 0 < cGap :=
    inv_pos.mpr (mul_pos (by norm_num) hKPos)
  refine Exists.intro cHeight (Exists.intro cGap
    (And.intro hHeightPos (And.intro hGapPos ?_)))
  intro N _hN hNLower chi hchi hPrimitive hchiSquare p hpIm hpHeight
  let Q := K * Real.log N
  have hLogNLower : Real.log 3 ≤ Real.log N :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hNLower)
  have hLogNPos : 0 < Real.log N := hLogThree.trans_le hLogNLower
  have hQPos : 0 < Q := mul_pos hKPos hLogNPos
  have hInvLogNonneg : 0 ≤ (Real.log 3)⁻¹ := (inv_pos.mpr hLogThree).le
  have hInvLogN : 1 ≤ (Real.log 3)⁻¹ * Real.log N := by
    have hScaled := mul_le_mul_of_nonneg_left hLogNLower hInvLogNonneg
    have hCancel : (Real.log 3)⁻¹ * Real.log 3 = 1 := by field_simp
    rw [hCancel] at hScaled
    exact hScaled
  have hQOne : 1 ≤ Q := by
    have hK0LogNonneg : 0 ≤ K0 * Real.log N :=
      mul_nonneg hK0Pos.le hLogNPos.le
    dsimp [Q, K]
    nlinarith
  have hCoreK : forall sigma : Real, 1 < sigma -> sigma ≤ 2 ->
      2 * (sigma -
        (Complex.Hadamard.divisorZeroIndex₀_val p).re) /
        ((sigma -
          (Complex.Hadamard.divisorZeroIndex₀_val p).re) ^ 2 +
          (Complex.Hadamard.divisorZeroIndex₀_val p).im ^ 2) ≤
        (sigma - 1)⁻¹ + Q := by
    intro sigma hsigma hsigmaUpper
    have hCore0 := hCore hNLower hchi hPrimitive hchiSquare p hpIm
      hsigma hsigmaUpper
    have hCoefficient : K0 * Real.log N ≤ K * Real.log N := by
      apply mul_le_mul_of_nonneg_right
      · dsimp [K]
        exact le_add_of_nonneg_right hInvLogNonneg
      · exact hLogNPos.le
    exact hCore0.trans (by
      simpa [Q, add_comm] using
        add_le_add_left hCoefficient (sigma - 1)⁻¹)
  have hHeightIdentity : cHeight / Real.log N = (10 * Q)⁻¹ := by
    dsimp [cHeight, Q]
    field_simp
  have hHeightSmall :
      (Complex.Hadamard.divisorZeroIndex₀_val p).im < (10 * Q)⁻¹ := by
    rw [← hHeightIdentity]
    exact hpHeight
  have hGap := nonreal_core_inequality_implies_lowHeight_gap
    (symmetricCompletedLFunction_divisorZeroIndex₀_re_mem_Ioo
      hchi hPrimitive p).2 hpIm hQPos hQOne hHeightSmall hCoreK
  have hGapIdentity : cGap / Real.log N = (15 * Q)⁻¹ := by
    dsimp [cGap, Q]
    field_simp
  rw [hGapIdentity]
  exact hGap

end BombieriVinogradov.SiegelWalfisz
