import BombieriVinogradov.Assembly.SiegelWalfisz.ExplicitFormula.RetainedBandCardBound
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Cutoff.RetainedBandReciprocalBound
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Cutoff.RetainedZeroBand
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedZeroIndex
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedZeroValue
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Defs
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.Tactic.Ring

/-!
# Reciprocal-norm sums in positive retained zero bands

This module combines the logarithmic band-cardinality estimate with the
pointwise reciprocal decay supplied by a positive band index.
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

theorem exists_sum_norm_one_div_retainedCriticalZeroBand_le :
    exists C : Real, And (0 < C)
      (forall {N : Nat} [NeZero N], 3 <= N ->
        forall {chi : DirichletCharacter Complex N},
          Ne chi 1 -> DirichletCharacter.IsPrimitive chi ->
            forall (T : Real) (exceptional : Option Complex) (k : Nat),
              1 <= k ->
                Finset.sum (retainedCriticalZeroBand chi T exceptional k)
                    (fun p => norm (1 / symmetricCompletedZeroValue p)) <=
                  C * (Real.log N + Real.log ((k : Real) + 2)) /
                    (k : Real)) := by
  choose C hCPos hCard using exists_card_retainedCriticalZeroBand_le
  refine Exists.intro C (And.intro hCPos ?_)
  intro N inst hN chi hchi hPrimitive T exceptional k hk
  let band := retainedCriticalZeroBand chi T exceptional k
  have hkNat : 0 < k := Nat.zero_lt_of_lt hk
  have hkReal : 0 < (k : Real) := (Nat.cast_pos).2 hkNat
  have hInvNonneg : 0 <= 1 / (k : Real) :=
    le_of_lt ((one_div_pos).2 hkReal)
  have hSumNsmul := Finset.sum_le_card_nsmul band
    (fun p => norm (1 / symmetricCompletedZeroValue p)) (1 / (k : Real))
    (by
      intro p hp
      have hpBand :
          (retainedCriticalZeroBand chi T exceptional k :
            Set (SymmetricCompletedZeroIndex chi)) p := hp
      exact norm_one_div_retainedCriticalZeroBand_le_one_div hk hpBand)
  have hSum :
      Finset.sum band (fun p => norm (1 / symmetricCompletedZeroValue p)) <=
        (band.card : Real) * (1 / (k : Real)) := by
    simpa only [nsmul_eq_mul] using hSumNsmul
  have hCardBound :
      (band.card : Real) <=
        C * (Real.log N + Real.log ((k : Real) + 2)) := by
    simpa [band] using hCard hN hchi hPrimitive T exceptional k
  calc
    Finset.sum band (fun p => norm (1 / symmetricCompletedZeroValue p)) <=
        (band.card : Real) * (1 / (k : Real)) := hSum
    _ <= (C * (Real.log N + Real.log ((k : Real) + 2))) *
        (1 / (k : Real)) :=
      mul_le_mul_of_nonneg_right hCardBound hInvNonneg
    _ = C * (Real.log N + Real.log ((k : Real) + 2)) /
        (k : Real) := by ring

end BombieriVinogradov.SiegelWalfisz
