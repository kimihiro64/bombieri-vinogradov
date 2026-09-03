import BombieriVinogradov.Assembly.SiegelWalfisz.ExplicitFormula.RetainedBandWindowInclusion
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Cutoff.RetainedZeroBand
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Horizontal.ZeroHeightWindow
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Horizontal.ZeroHeightWindowCountBound
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedZeroIndex
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Defs
import Mathlib.NumberTheory.DirichletCharacter.Basic

/-!
# Cardinality of a retained absolute-height band
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

theorem card_retainedCriticalZeroBand_le_two_windows
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : Ne chi 1) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    (T : Real) (exceptional : Option Complex) (k : Nat) :
    (retainedCriticalZeroBand chi T exceptional k).card <=
      (zeroHeightWindow (chi := chi) (k : Real)).ncard +
        (zeroHeightWindow (chi := chi) (-(k : Real))).ncard := by
  let band := retainedCriticalZeroBand chi T exceptional k
  let pos : Set (SymmetricCompletedZeroIndex chi) :=
    zeroHeightWindow (chi := chi) (k : Real)
  let neg : Set (SymmetricCompletedZeroIndex chi) :=
    zeroHeightWindow (chi := chi) (-(k : Real))
  let combined : Set (SymmetricCompletedZeroIndex chi) :=
    Set.union pos neg
  have hPosFinite : Set.Finite pos := by
    simpa [pos] using
      finite_zeroHeightWindow hchi hPrimitive (k : Real)
  have hNegFinite : Set.Finite neg := by
    simpa [neg] using
      finite_zeroHeightWindow hchi hPrimitive (-(k : Real))
  have hCombinedFinite : Set.Finite combined := by
    dsimp [combined]
    exact hPosFinite.union hNegFinite
  have hSubset :
      forall p,
        (band : Set (SymmetricCompletedZeroIndex chi)) p ->
          combined p := by
    intro p hp
    change Or (pos p) (neg p)
    simpa [band, pos, neg] using
      mem_pos_or_neg_zeroHeightWindow_of_mem_retainedCriticalZeroBand hp
  have hBandNcard :
      (band : Set (SymmetricCompletedZeroIndex chi)).ncard <=
        combined.ncard :=
    Set.ncard_le_ncard hSubset hCombinedFinite
  have hCard : band.card <= combined.ncard := by
    simpa only [Set.ncard_coe_finset] using hBandNcard
  have hUnion : combined.ncard <= pos.ncard + neg.ncard := by
    dsimp [combined]
    exact Set.ncard_union_le pos neg
  simpa [band, pos, neg] using hCard.trans hUnion

end BombieriVinogradov.SiegelWalfisz
