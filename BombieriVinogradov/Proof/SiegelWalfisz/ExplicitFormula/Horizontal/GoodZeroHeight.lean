import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Horizontal.ZeroHeightScale
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Horizontal.ZeroHeightSelection
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Horizontal.ZeroHeightWindowCountBound
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Good horizontal heights with logarithmic zero separation

This module substitutes the logarithmic zero-window cardinality estimate into
the cardinality-based selection theorem and absorbs all constants into one
absolute positive constant.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

/-- One absolute positive constant selects a height in the next unit interval
whose distance from every completed zero is bounded below by the reciprocal
of the shared modulus-height logarithmic scale. -/
theorem exists_goodZeroHeight :
    exists C : Real, And (0 < C)
      (forall {N : Nat} [NeZero N], 3 <= N ->
        forall {chi : DirichletCharacter Complex N},
          Ne chi 1 -> DirichletCharacter.IsPrimitive chi ->
            forall T : Real, 2 <= T ->
              exists Tprime : Real, And (T <= Tprime)
                (And (Tprime <= T + 1)
                  (forall p : SymmetricCompletedZeroIndex chi,
                    1 / (C * zeroHeightLogScale N T) <=
                      abs (Tprime -
                        (symmetricCompletedZeroValue p).im)))) := by
  choose C hCPos hCount using exists_ncard_zeroHeightWindow_le
  refine Exists.intro (2 * C + 4) (And.intro (by linarith) ?_)
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
  have hScaleOne : 1 <= zeroHeightLogScale N T := by
    dsimp [zeroHeightLogScale]
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
      Real.log N + Real.log (abs (T + 1 / 2) + 2) <=
        zeroHeightLogScale N T := by
    dsimp [zeroHeightLogScale]
    linarith
  have hCountCenter :
      ((zeroHeightWindow (chi := chi) (T + 1 / 2)).ncard : Real) <=
        C * (Real.log N + Real.log (abs (T + 1 / 2) + 2)) :=
    (hCount hN hchi hPrimitive (T + 1 / 2)).2
  have hCountScale :
      ((zeroHeightWindow (chi := chi) (T + 1 / 2)).ncard : Real) <=
        C * zeroHeightLogScale N T :=
    hCountCenter.trans
      (mul_le_mul_of_nonneg_left hBaseLeScale (le_of_lt hCPos))
  choose Tprime hTprimeLower hTprimeUpper hGap using
    exists_zeroHeight_separated_by_ncard hchi hPrimitive T
  refine Exists.intro Tprime
    (And.intro hTprimeLower (And.intro hTprimeUpper ?_))
  intro p
  have hActualDenPos :
      0 < 2 *
        (((zeroHeightWindow (chi := chi) (T + 1 / 2)).ncard : Real) + 2) := by
    positivity
  have hDenLe :
      2 * (((zeroHeightWindow (chi := chi)
          (T + 1 / 2)).ncard : Real) + 2) <=
        (2 * C + 4) * zeroHeightLogScale N T := by
    nlinarith
  exact
    (one_div_le_one_div_of_le hActualDenPos hDenLe).trans (hGap p)

end BombieriVinogradov.SiegelWalfisz
