import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Cutoff.DifferenceWindowInclusion
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Horizontal.TwoSidedZeroHeightWindowCountBound
import Mathlib.Data.Set.Card
import Mathlib.Tactic.Linarith

/-!
# Cardinality of newly retained zeros

This module bounds the number of multiplicity indices added between nearby
cutoffs by the shared modulus-height logarithmic scale.
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

theorem exists_card_retainedCriticalZeroCutoffDifference_le :
    exists C : Real, And (0 < C)
      (forall {N : Nat} [NeZero N], 3 <= N ->
        forall {chi : DirichletCharacter Complex N},
          Ne chi 1 -> DirichletCharacter.IsPrimitive chi ->
            forall {T Tprime : Real}, 2 <= T -> Tprime <= T + 1 ->
              forall exceptional : Option Complex,
                ((retainedCriticalZeroCutoffDifference
                    chi T Tprime exceptional).card : Real) <=
                  C * zeroHeightLogScale N T) := by
  choose C hCPos hTwoSided using
    exists_twoSidedZeroHeightDenominator_le
  refine Exists.intro C (And.intro hCPos ?_)
  intro N inst hN chi hchi hPrimitive T Tprime hT hTop exceptional
  let diff :=
    retainedCriticalZeroCutoffDifference chi T Tprime exceptional
  let pos : Set (SymmetricCompletedZeroIndex chi) :=
    zeroHeightWindow (chi := chi) (T + 1 / 2)
  let neg : Set (SymmetricCompletedZeroIndex chi) :=
    zeroHeightWindow (chi := chi) (-(T + 1 / 2))
  let combined : Set (SymmetricCompletedZeroIndex chi) :=
    Set.union pos neg
  have hPosFinite : Set.Finite pos := by
    simpa [pos] using
      finite_zeroHeightWindow hchi hPrimitive (T + 1 / 2)
  have hNegFinite : Set.Finite neg := by
    simpa [neg] using
      finite_zeroHeightWindow hchi hPrimitive (-(T + 1 / 2))
  have hCombinedFinite : Set.Finite combined := by
    dsimp [combined]
    exact hPosFinite.union hNegFinite
  have hDifferenceSubset :
      forall p, (diff : Set (SymmetricCompletedZeroIndex chi)) p ->
        combined p := by
    intro p hp
    change Or (pos p) (neg p)
    simpa [diff, pos, neg] using
      mem_zeroHeightWindow_or_neg_of_mem_cutoffDifference hTop hp
  have hDifferenceNcard :
      (diff : Set (SymmetricCompletedZeroIndex chi)).ncard <=
        combined.ncard :=
    Set.ncard_le_ncard hDifferenceSubset hCombinedFinite
  have hCardNat : diff.card <= combined.ncard := by
    simpa only [Set.ncard_coe_finset] using hDifferenceNcard
  have hUnionNcard :
      combined.ncard <= pos.ncard + neg.ncard := by
    dsimp [combined]
    exact Set.ncard_union_le pos neg
  have hCast :
      (diff.card : Real) <= ((pos.ncard + neg.ncard : Nat) : Real) :=
    (Nat.cast_le).2 (hCardNat.trans hUnionNcard)
  have hTwoSidedBound :
      2 * (((pos.ncard + neg.ncard : Nat) : Real) + 2) <=
        C * zeroHeightLogScale N T := by
    simpa [pos, neg] using hTwoSided hN hchi hPrimitive T hT
  have hCombinedNonneg :
      0 <= ((pos.ncard + neg.ncard : Nat) : Real) :=
    Nat.cast_nonneg _
  have hCombinedBound :
      ((pos.ncard + neg.ncard : Nat) : Real) <=
        C * zeroHeightLogScale N T := by
    linarith
  exact hCast.trans hCombinedBound

end BombieriVinogradov.SiegelWalfisz
