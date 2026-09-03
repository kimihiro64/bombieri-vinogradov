import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Horizontal.ZeroHeightScale
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Horizontal.ZeroHeightWindowCountBound
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Two-sided zero-window count normalization

This module bounds the combined positive and negative unit-window counts by
the shared modulus-height logarithmic scale used for horizontal contours.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem exists_twoSidedZeroHeightDenominator_le :
    exists C : Real, And (0 < C)
      (forall {N : Nat} [NeZero N], 3 <= N ->
        forall {chi : DirichletCharacter Complex N},
          Ne chi 1 -> DirichletCharacter.IsPrimitive chi ->
            forall T : Real, 2 <= T ->
              2 *
                  ((((zeroHeightWindow (chi := chi) (T + 1 / 2)).ncard +
                    (zeroHeightWindow (chi := chi) (-(T + 1 / 2))).ncard :
                      Nat) : Real) + 2) <=
                C * zeroHeightLogScale N T) := by
  choose C0 hC0Pos hCount using exists_ncard_zeroHeightWindow_le
  let C : Real := 4 * C0 + 4
  have hCPos : 0 < C := by
    dsimp [C]
    linarith
  refine Exists.intro C (And.intro hCPos ?_)
  intro N inst hN chi hchi hPrimitive T hT
  have hNOneNat : 1 < N :=
    lt_of_lt_of_le (by norm_num) hN
  have hNOneRealRaw : ((1 : Nat) : Real) < (N : Real) :=
    (Nat.cast_lt).2 hNOneNat
  have hNOneReal : (1 : Real) < (N : Real) := by
    simpa using hNOneRealRaw
  have hLogNPos : 0 < Real.log N :=
    Real.log_pos hNOneReal
  have hTArgOne : (1 : Real) < T + 3 := by
    linarith
  have hLogTPos : 0 < Real.log (T + 3) :=
    Real.log_pos hTArgOne
  let L : Real := zeroHeightLogScale N T
  have hScaleOne : 1 <= L := by
    dsimp [L, zeroHeightLogScale]
    linarith
  have hCenterArgPos : 0 < abs (T + 1 / 2) + 2 := by
    positivity
  have hCenterArgLe : abs (T + 1 / 2) + 2 <= T + 3 := by
    rw [abs_of_nonneg (by linarith)]
    linarith
  have hCenterLogLe :
      Real.log (abs (T + 1 / 2) + 2) <= Real.log (T + 3) :=
    Real.log_le_log hCenterArgPos hCenterArgLe
  have hBaseLeScale :
      Real.log N + Real.log (abs (T + 1 / 2) + 2) <= L := by
    dsimp [L, zeroHeightLogScale]
    linarith
  have hPosCountRaw :
      ((zeroHeightWindow (chi := chi) (T + 1 / 2)).ncard : Real) <=
        C0 * (Real.log N + Real.log (abs (T + 1 / 2) + 2)) :=
    (hCount hN hchi hPrimitive (T + 1 / 2)).2
  have hPosCountScale :
      ((zeroHeightWindow (chi := chi) (T + 1 / 2)).ncard : Real) <=
        C0 * L :=
    hPosCountRaw.trans
      (mul_le_mul_of_nonneg_left hBaseLeScale hC0Pos.le)
  have hNegCountRaw :
      ((zeroHeightWindow (chi := chi) (-(T + 1 / 2))).ncard : Real) <=
        C0 *
          (Real.log N + Real.log (abs (-(T + 1 / 2)) + 2)) :=
    (hCount hN hchi hPrimitive (-(T + 1 / 2))).2
  have hNegBaseLeScale :
      Real.log N + Real.log (abs (-(T + 1 / 2)) + 2) <= L := by
    simpa only [abs_neg] using hBaseLeScale
  have hNegCountScale :
      ((zeroHeightWindow (chi := chi) (-(T + 1 / 2))).ncard : Real) <=
        C0 * L :=
    hNegCountRaw.trans
      (mul_le_mul_of_nonneg_left hNegBaseLeScale hC0Pos.le)
  have hCombinedCountScale :
      (((zeroHeightWindow (chi := chi) (T + 1 / 2)).ncard +
          (zeroHeightWindow (chi := chi) (-(T + 1 / 2))).ncard : Nat) :
        Real) <= 2 * C0 * L := by
    rw [Nat.cast_add]
    linarith
  dsimp [C]
  nlinarith

end BombieriVinogradov.SiegelWalfisz
