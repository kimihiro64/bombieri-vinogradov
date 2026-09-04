import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.CriticalStripZeroValues
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Definitions
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Exceptional.RetainedZeroRightGap
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Exceptional.ZeroFreeData
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.RetainedZeroValues
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedZeroIndex
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedZeroValue
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Defs
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Retained-zero right gap at a uniform height cutoff

The pointwise zero-free denominator is enlarged to one common denominator
for the entire retained finite sum. Primitivity is retained explicitly.
-/
set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem retainedCriticalZero_re_le_cutoff
    {c : Real} (hc : 0 < c) {N : Nat} [NeZero N]
    {chi : _root_.DirichletCharacter Complex N} (hN : 3 <= N) (hchi : Ne chi 1)
    (hPrimitive : _root_.DirichletCharacter.IsPrimitive chi)
    (hData : ExplicitFormulaZeroFreeData c chi)
    (e : Option Complex) (hChoice : IsExceptionalZeroChoice c chi e)
    {T : Real} {p : SymmetricCompletedZeroIndex chi}
    (hp : (retainedCriticalZeroIndices chi T e : Set (SymmetricCompletedZeroIndex chi)) p) :
    (symmetricCompletedZeroValue p).re <=
      1 - c / (Real.log N + Real.log (T + 2)) := by
  have hMem := (mem_retainedCriticalZeroIndices_iff
    (chi := chi) (T := T) (exceptional := e) (p := p)).mp hp
  have hStrip : And (0 < (symmetricCompletedZeroValue p).re)
      (And ((symmetricCompletedZeroValue p).re < 1)
        (abs (symmetricCompletedZeroValue p).im < T)) := by
    simpa only [symmetricCompletedZeroValue] using
      (mem_criticalStripZeroTruncation_iff.mp hMem.1)
  have hZero : chi.LFunction (symmetricCompletedZeroValue p) = 0 := by
    simpa only [symmetricCompletedZeroValue] using
      LFunction_eq_zero_of_mem_criticalStripZeroTruncation hchi hPrimitive hMem.1
  have hRetained : IsRetainedZero e (symmetricCompletedZeroValue p) := by
    simpa only [symmetricCompletedZeroValue] using hMem.2
  have hRight := retainedLFunctionZero_gap_from_one hc hN
    hData.regularGap hData.realUnique hChoice hZero hStrip.1 hStrip.2.1 hRetained
  have hThree : (3 : Real) <= (N : Real) := Nat.cast_le.mpr hN
  have hLogThree : 0 < Real.log (3 : Real) := Real.log_pos (by norm_num)
  have hLogNPos : 0 < Real.log N :=
    hLogThree.trans_le (Real.log_le_log (by norm_num) hThree)
  have hHeightNonneg : 0 <= Real.log (abs (symmetricCompletedZeroValue p).im + 2) := by
    apply Real.log_nonneg
    linarith [abs_nonneg (symmetricCompletedZeroValue p).im]
  have hDenomPos : 0 < Real.log N +
      Real.log (abs (symmetricCompletedZeroValue p).im + 2) := by linarith
  have hLogHeight : Real.log (abs (symmetricCompletedZeroValue p).im + 2) <=
      Real.log (T + 2) :=
    Real.log_le_log (by linarith [abs_nonneg (symmetricCompletedZeroValue p).im])
      (by linarith [hStrip.2.2])
  have hCompare : c / (Real.log N + Real.log (T + 2)) <=
      c / (Real.log N + Real.log (abs (symmetricCompletedZeroValue p).im + 2)) :=
    div_le_div_of_nonneg_left hc.le hDenomPos (by linarith)
  linarith

end BombieriVinogradov.SiegelWalfisz
