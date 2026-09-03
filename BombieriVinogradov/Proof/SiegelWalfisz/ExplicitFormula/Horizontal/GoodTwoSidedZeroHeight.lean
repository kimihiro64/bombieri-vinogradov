import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Horizontal.TwoSidedZeroHeightSelection
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Horizontal.TwoSidedZeroHeightWindowCountBound
import Mathlib.Tactic.Positivity

/-!
# A logarithmically separated two-sided zero height

This module selects one height whose positive and negative ordinates are both
uniformly separated from every multiplicity-indexed completed zero.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem exists_goodTwoSidedZeroHeight :
    exists C : Real, And (0 < C)
      (forall {N : Nat} [NeZero N], 3 <= N ->
        forall {chi : DirichletCharacter Complex N},
          Ne chi 1 -> DirichletCharacter.IsPrimitive chi ->
            forall T : Real, 2 <= T ->
              exists Tprime : Real, And (T <= Tprime)
                (And (Tprime <= T + 1)
                  (forall p : SymmetricCompletedZeroIndex chi,
                    And
                      (1 / (C * zeroHeightLogScale N T) <=
                        abs (Tprime -
                          (symmetricCompletedZeroValue p).im))
                      (1 / (C * zeroHeightLogScale N T) <=
                        abs ((-Tprime) -
                          (symmetricCompletedZeroValue p).im))))) := by
  choose C hCPos hDenBound using
    exists_twoSidedZeroHeightDenominator_le
  refine Exists.intro C (And.intro hCPos ?_)
  intro N inst hN chi hchi hPrimitive T hT
  choose Tprime hTprimeLower hTprimeUpper hGap using
    exists_twoSidedZeroHeight_separated_by_ncard hchi hPrimitive T
  refine Exists.intro Tprime
    (And.intro hTprimeLower (And.intro hTprimeUpper ?_))
  intro p
  have hActualDenPos :
      0 < 2 *
        ((((zeroHeightWindow (chi := chi) (T + 1 / 2)).ncard +
          (zeroHeightWindow (chi := chi) (-(T + 1 / 2))).ncard : Nat) :
            Real) + 2) := by
    positivity
  have hRadiusMono :
      1 / (C * zeroHeightLogScale N T) <=
        1 / (2 *
          ((((zeroHeightWindow (chi := chi) (T + 1 / 2)).ncard +
            (zeroHeightWindow (chi := chi) (-(T + 1 / 2))).ncard : Nat) :
              Real) + 2)) :=
    one_div_le_one_div_of_le hActualDenPos
      (hDenBound hN hchi hPrimitive T hT)
  exact And.intro
    (hRadiusMono.trans (hGap p).1)
    (hRadiusMono.trans (hGap p).2)

end BombieriVinogradov.SiegelWalfisz
