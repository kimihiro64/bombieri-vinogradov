import BombieriVinogradov.Assembly.SiegelWalfisz.ExplicitFormula.RetainedBandCardToWindows
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
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Cardinality bound for retained zero bands

This module combines the two-window covering of a retained absolute-height
band with the uniform logarithmic zero-window count.
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

theorem exists_card_retainedCriticalZeroBand_le :
    exists C : Real, And (0 < C)
      (forall {N : Nat} [NeZero N], 3 <= N ->
        forall {chi : DirichletCharacter Complex N},
          Ne chi 1 -> DirichletCharacter.IsPrimitive chi ->
            forall (T : Real) (exceptional : Option Complex) (k : Nat),
              ((retainedCriticalZeroBand chi T exceptional k).card : Real) <=
                C * (Real.log N + Real.log ((k : Real) + 2))) := by
  choose C hCPos hCount using exists_ncard_zeroHeightWindow_le
  refine Exists.intro (2 * C) (And.intro (mul_pos (by norm_num) hCPos) ?_)
  intro N inst hN chi hchi hPrimitive T exceptional k
  have hCardNat :
      (retainedCriticalZeroBand chi T exceptional k).card <=
        (zeroHeightWindow (chi := chi) (k : Real)).ncard +
          (zeroHeightWindow (chi := chi) (-(k : Real))).ncard :=
    card_retainedCriticalZeroBand_le_two_windows
      hchi hPrimitive T exceptional k
  have hCardReal :
      ((retainedCriticalZeroBand chi T exceptional k).card : Real) <=
        ((zeroHeightWindow (chi := chi) (k : Real)).ncard : Real) +
          ((zeroHeightWindow (chi := chi) (-(k : Real))).ncard : Real) := by
    simpa only [Nat.cast_add] using
      ((Nat.cast_le).2 hCardNat)
  have hkNonneg : 0 <= (k : Real) := Nat.cast_nonneg k
  have hPosBound :
      ((zeroHeightWindow (chi := chi) (k : Real)).ncard : Real) <=
        C * (Real.log N + Real.log ((k : Real) + 2)) := by
    simpa [abs_of_nonneg hkNonneg] using
      (hCount hN hchi hPrimitive (k : Real)).2
  have hNegBound :
      ((zeroHeightWindow (chi := chi) (-(k : Real))).ncard : Real) <=
        C * (Real.log N + Real.log ((k : Real) + 2)) := by
    simpa [abs_neg, abs_of_nonneg hkNonneg] using
      (hCount hN hchi hPrimitive (-(k : Real))).2
  nlinarith

end BombieriVinogradov.SiegelWalfisz
