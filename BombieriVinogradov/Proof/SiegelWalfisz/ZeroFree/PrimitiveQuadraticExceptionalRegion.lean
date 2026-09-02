import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.PrimitiveQuadraticNonrealZeroGap
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.PrimitiveQuadraticRealZeroSimplicity

/-!
# Primitive quadratic exceptional region

This module exposes the nonreal gap, real-index uniqueness, and completed-zero
simplicity under one absolute positive constant.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem exists_primitive_quadratic_exceptionalRegion :
    exists c : Real, 0 < c ∧
      forall {N : Nat} [NeZero N], 3 ≤ N ->
        forall {chi : DirichletCharacter Complex N},
          chi ≠ 1 -> DirichletCharacter.IsPrimitive chi -> chi ^ 2 = 1 ->
            (forall p : SymmetricCompletedZeroIndex chi,
              (Complex.Hadamard.divisorZeroIndex₀_val p).im ≠ 0 ->
                c / (Real.log N + Real.log
                  (|(Complex.Hadamard.divisorZeroIndex₀_val p).im| + 2)) ≤
                  1 - (Complex.Hadamard.divisorZeroIndex₀_val p).re) ∧
            (forall p q : SymmetricCompletedZeroIndex chi,
              (Complex.Hadamard.divisorZeroIndex₀_val p).im = 0 ->
              (Complex.Hadamard.divisorZeroIndex₀_val q).im = 0 ->
              1 - (Complex.Hadamard.divisorZeroIndex₀_val p).re ≤
                c / Real.log N ->
              1 - (Complex.Hadamard.divisorZeroIndex₀_val q).re ≤
                c / Real.log N -> p = q) ∧
            (forall p : SymmetricCompletedZeroIndex chi,
              (Complex.Hadamard.divisorZeroIndex₀_val p).im = 0 ->
              1 - (Complex.Hadamard.divisorZeroIndex₀_val p).re ≤
                c / Real.log N ->
                analyticOrderNatAt (symmetricCompletedLFunction chi)
                  (Complex.Hadamard.divisorZeroIndex₀_val p) = 1) := by
  obtain ⟨cNonreal, hNonrealPos, hNonreal⟩ :=
    exists_primitive_quadratic_nonrealZero_gap
  obtain ⟨cUnique, hUniquePos, hUnique⟩ :=
    exists_primitive_quadratic_realZero_unique
  obtain ⟨cSimple, hSimplePos, hSimple⟩ :=
    exists_primitive_quadratic_realZero_simple
  let c : Real := min cNonreal (min cUnique cSimple)
  have hcPos : 0 < c := by
    dsimp [c]
    exact lt_min hNonrealPos (lt_min hUniquePos hSimplePos)
  have hcNonreal : c ≤ cNonreal := by
    dsimp [c]
    exact min_le_left _ _
  have hcUnique : c ≤ cUnique := by
    dsimp [c]
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hcSimple : c ≤ cSimple := by
    dsimp [c]
    exact (min_le_right _ _).trans (min_le_right _ _)
  refine Exists.intro c (And.intro hcPos ?_)
  intro N _hN hNLower chi hchi hPrimitive hchiSquare
  have hLogThree : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hLogNLower : Real.log 3 ≤ Real.log N :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hNLower)
  have hLogNPos : 0 < Real.log N := hLogThree.trans_le hLogNLower
  apply And.intro
  · intro p hpNonreal
    let L : Real := Real.log N + Real.log
      (|(Complex.Hadamard.divisorZeroIndex₀_val p).im| + 2)
    have hHeightNonneg :
        0 ≤ Real.log
          (|(Complex.Hadamard.divisorZeroIndex₀_val p).im| + 2) := by
      apply Real.log_nonneg
      linarith [abs_nonneg
        (Complex.Hadamard.divisorZeroIndex₀_val p).im]
    have hLPos : 0 < L := by
      dsimp [L]
      linarith
    have hNumerator : c / L ≤ cNonreal / L :=
      (div_le_div_iff_of_pos_right hLPos).2 hcNonreal
    have hGap := hNonreal hNLower hchi hPrimitive hchiSquare p hpNonreal
    exact hNumerator.trans (by simpa [L] using hGap)
  · apply And.intro
    · intro p q hpReal hqReal hpGap hqGap
      have hScale : c / Real.log N ≤ cUnique / Real.log N :=
        (div_le_div_iff_of_pos_right hLogNPos).2 hcUnique
      exact hUnique hNLower hchi hPrimitive p q hpReal hqReal
        (hpGap.trans hScale) (hqGap.trans hScale)
    · intro p hpReal hpGap
      have hScale : c / Real.log N ≤ cSimple / Real.log N :=
        (div_le_div_iff_of_pos_right hLogNPos).2 hcSimple
      exact hSimple hNLower hchi hPrimitive p hpReal
        (hpGap.trans hScale)

end BombieriVinogradov.SiegelWalfisz
