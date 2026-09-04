import BombieriVinogradov.Helpers.ComplexAnalysis.CpowDecayBound
import BombieriVinogradov.Proof.SiegelWalfisz.CharacterEstimate.RetainedCutoffGap
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Cutoff.ASCIIExpansion
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Definitions
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Exceptional.ZeroFreeData
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.RetainedZeroValues
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedZeroIndex
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedZeroValue
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Defs
import Mathlib.NumberTheory.DirichletCharacter.Basic

/-!
# Exponential decay of the retained zero sum

The common zero-free gap supplies a decay factor in every summand.
The finite sum retains the original zero indices and their multiplicities.
-/
set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem norm_truncatedCriticalZeroSum_le_exp_gap_mul_reciprocal_sum
    {c : Real} (hc : 0 < c) {N x : Nat} [NeZero N]
    {chi : DirichletCharacter Complex N} (hN : 3 <= N) (hchi : Ne chi 1)
    (hPrimitive : DirichletCharacter.IsPrimitive chi)
    (hData : ExplicitFormulaZeroFreeData c chi)
    (e : Option Complex) (hChoice : IsExceptionalZeroChoice c chi e)
    (hx : 1 <= x) (T : Real) :
    norm (truncatedCriticalZeroSum chi x T e) <=
      ((x : Real) * Real.exp (-(c / (Real.log N + Real.log (T + 2))) * Real.log x)) *
        Finset.sum (retainedCriticalZeroIndices chi T e)
          (fun p => norm ((1 : Complex) / symmetricCompletedZeroValue p)) := by
  have hxReal : (1 : Real) <= (x : Real) := by
    have hRaw : ((1 : Nat) : Real) <= (x : Real) := Nat.cast_le.mpr hx
    simpa only [Nat.cast_one] using hRaw
  have hTerm (p : SymmetricCompletedZeroIndex chi)
      (hp : (retainedCriticalZeroIndices chi T e :
        Set (SymmetricCompletedZeroIndex chi)) p) :
      norm ((x : Complex) ^ symmetricCompletedZeroValue p /
        symmetricCompletedZeroValue p) <=
      ((x : Real) * Real.exp (-(c / (Real.log N + Real.log (T + 2))) * Real.log x)) *
        norm ((1 : Complex) / symmetricCompletedZeroValue p) := by
    have hGap := retainedCriticalZero_re_le_cutoff hc hN hchi hPrimitive hData e hChoice hp
    have h := BombieriVinogradov.ComplexAnalysis.norm_real_cpow_div_le_exp_gap_mul_reciprocal
      hxReal hGap
    simpa only [Complex.ofReal_natCast] using h
  rw [truncatedCriticalZeroSum_eq_sum_symmetricCompletedZeroValue]
  calc
    norm (Finset.sum (retainedCriticalZeroIndices chi T e)
        (fun p => (x : Complex) ^ symmetricCompletedZeroValue p /
          symmetricCompletedZeroValue p)) <=
      Finset.sum (retainedCriticalZeroIndices chi T e)
        (fun p => norm ((x : Complex) ^ symmetricCompletedZeroValue p /
          symmetricCompletedZeroValue p)) := norm_sum_le _ _
    _ <= Finset.sum (retainedCriticalZeroIndices chi T e)
        (fun p => ((x : Real) *
          Real.exp (-(c / (Real.log N + Real.log (T + 2))) * Real.log x)) *
            norm ((1 : Complex) / symmetricCompletedZeroValue p)) :=
      Finset.sum_le_sum (fun p hp => hTerm p hp)
    _ = ((x : Real) *
          Real.exp (-(c / (Real.log N + Real.log (T + 2))) * Real.log x)) *
        Finset.sum (retainedCriticalZeroIndices chi T e)
          (fun p => norm ((1 : Complex) / symmetricCompletedZeroValue p)) :=
      (Finset.mul_sum (retainedCriticalZeroIndices chi T e)
        (fun p => norm ((1 : Complex) / symmetricCompletedZeroValue p))
        ((x : Real) *
          Real.exp (-(c / (Real.log N + Real.log (T + 2))) * Real.log x))).symm

end BombieriVinogradov.SiegelWalfisz
