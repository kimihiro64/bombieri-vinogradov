import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.PrimitiveQuadraticHighHeightGap
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.PrimitiveQuadraticLowHeightGap

/-!
# Uniform gap for positive-height primitive quadratic zeros

This module joins the low- and high-height branches at the low-height
threshold and weakens both conclusions to one common logarithmic scale.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem exists_primitive_quadratic_positiveZero_gap :
    exists c : Real, 0 < c ∧
      forall {N : Nat} [NeZero N], 3 ≤ N ->
        forall {chi : DirichletCharacter Complex N},
          chi ≠ 1 -> DirichletCharacter.IsPrimitive chi -> chi ^ 2 = 1 ->
            forall p : SymmetricCompletedZeroIndex chi,
              0 < (Complex.Hadamard.divisorZeroIndex₀_val p).im ->
                c / (Real.log N + Real.log
                  (|(Complex.Hadamard.divisorZeroIndex₀_val p).im| + 2)) ≤
                  1 - (Complex.Hadamard.divisorZeroIndex₀_val p).re := by
  obtain ⟨cHeight, cLow, hHeightPos, hLowPos, hLow⟩ :=
    exists_primitive_quadratic_lowHeight_nonreal_gap
  obtain ⟨cHigh, hHighPos, hHigh⟩ :=
    exists_primitive_quadratic_highHeight_gap cHeight hHeightPos
  let c : Real := min cLow cHigh
  have hcPos : 0 < c := by
    dsimp [c]
    exact lt_min hLowPos hHighPos
  refine Exists.intro c (And.intro hcPos ?_)
  intro N _hN hNLower chi hchi hPrimitive hchiSquare p hpIm
  let t : Real := (Complex.Hadamard.divisorZeroIndex₀_val p).im
  let L : Real := Real.log N + Real.log (|t| + 2)
  have hLogThree : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hLogNLower : Real.log 3 ≤ Real.log N :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hNLower)
  have hLogNPos : 0 < Real.log N := hLogThree.trans_le hLogNLower
  have hLogHeightNonneg : 0 ≤ Real.log (|t| + 2) := by
    apply Real.log_nonneg
    linarith [abs_nonneg t]
  have hLPos : 0 < L := by
    dsimp [L]
    linarith
  have hLogNLeL : Real.log N ≤ L := by
    dsimp [L]
    linarith
  by_cases hSmall : t < cHeight / Real.log N
  · have hLowGap := hLow hNLower hchi hPrimitive hchiSquare p
      (by simpa [t] using hpIm) hSmall
    have hNumerator : c / L ≤ cLow / L :=
      (div_le_div_iff_of_pos_right hLPos).2 (by
        dsimp [c]
        exact min_le_left _ _)
    have hScale : cLow / L ≤ cLow / Real.log N :=
      div_le_div_of_nonneg_left hLowPos.le hLogNPos hLogNLeL
    exact hNumerator.trans (hScale.trans (by simpa [t] using hLowGap))
  · have hHighGap := hHigh hNLower hchi hPrimitive hchiSquare p
      (by
        simpa [t] using le_of_not_gt hSmall)
    have hNumerator : c / L ≤ cHigh / L :=
      (div_le_div_iff_of_pos_right hLPos).2 (by
        dsimp [c]
        exact min_le_right _ _)
    exact hNumerator.trans (by simpa [t, L] using hHighGap)

end BombieriVinogradov.SiegelWalfisz
