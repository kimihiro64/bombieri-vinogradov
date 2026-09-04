import BombieriVinogradov.Assembly.SiegelWalfisz.ExplicitFormula.RetainedBandSumBound
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Cutoff.WeightedSumNorm
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Definitions
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Exceptional.ZeroFreeData
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.RetainedZeroValues
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.SourceScale.EndpointTwo
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedZeroIndex
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedZeroValue
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.Tactic.Choose
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The retained zero sum at the lower endpoint

The height-two reciprocal estimate and the critical-strip power bound
give one logarithmic constant uniform in the primitive character.
-/
set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem exists_norm_truncatedCriticalZeroSum_two_le_sourceScale
    {c : Real} (hc : 0 < c) :
    exists C : Real, And (0 < C)
      (forall {N : Nat} [NeZero N], 3 <= N ->
        forall {chi : DirichletCharacter Complex N},
          Ne chi 1 -> DirichletCharacter.IsPrimitive chi ->
          ExplicitFormulaZeroFreeData c chi ->
          forall (exceptional : Option Complex),
            IsExceptionalZeroChoice c chi exceptional ->
              norm (truncatedCriticalZeroSum chi 2 2 exceptional) <=
                C * (Real.log ((N * 2 : Nat) : Real)) ^ 2) := by
  choose A hA hReciprocal using
    exists_sum_norm_one_div_retainedCriticalZeroIndices_le hc
  refine Exists.intro (8 * A) (And.intro (by positivity) ?_)
  intro N inst hN chi hchi hPrimitive hData exceptional hChoice
  have hRaw := hReciprocal hN hchi hPrimitive
    hData.regularGap hData.realUnique exceptional hChoice 2 (by norm_num)
  have hReciprocalBound :
      Finset.sum (retainedCriticalZeroIndices chi 2 exceptional)
        (fun p => norm ((1 : Complex) / symmetricCompletedZeroValue p)) <=
      A * (Real.log N + Real.log 4) ^ 2 := by
    norm_num at hRaw
    simpa using hRaw
  have hWeight : norm (truncatedCriticalZeroSum chi 2 2 exceptional) <=
      2 * Finset.sum (retainedCriticalZeroIndices chi 2 exceptional)
        (fun p => norm ((1 : Complex) / symmetricCompletedZeroValue p)) := by
    simpa using norm_truncatedCriticalZeroSum_le_argument_mul_reciprocal_sum
      (x := 2) hchi hPrimitive (by norm_num) 2 exceptional
  have hLogs := (endpointTwo_sourceLog_bounds hN).2
  calc
    norm (truncatedCriticalZeroSum chi 2 2 exceptional) <=
        2 * Finset.sum (retainedCriticalZeroIndices chi 2 exceptional)
          (fun p => norm ((1 : Complex) / symmetricCompletedZeroValue p)) := hWeight
    _ <= 2 * (A * (Real.log N + Real.log 4) ^ 2) :=
      mul_le_mul_of_nonneg_left hReciprocalBound (by norm_num)
    _ <= 2 * (A * (4 * (Real.log ((N * 2 : Nat) : Real)) ^ 2)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hLogs hA.le) (by norm_num)
    _ = (8 * A) * (Real.log ((N * 2 : Nat) : Real)) ^ 2 := by ring

end BombieriVinogradov.SiegelWalfisz
