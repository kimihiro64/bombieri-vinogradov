import BombieriVinogradov.Helpers.ComplexAnalysis.CpowLinearBound
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Cutoff.ASCIIExpansion
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Definitions
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.RetainedZeroValues
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedZeroIndex
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedZeroValue
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.DirichletCharacter.Basic

/-!
# A weighted retained-zero sum bound

Every completed primitive zero lies in the critical strip. The linear
complex-power bound reduces the full retained sum to its reciprocal sum.
-/
set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem norm_truncatedCriticalZeroSum_le_argument_mul_reciprocal_sum
    {N x : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : Ne chi 1) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    (hx : 1 <= x) (T : Real) (exceptional : Option Complex) :
    norm (truncatedCriticalZeroSum chi x T exceptional) <=
      (x : Real) *
        Finset.sum (retainedCriticalZeroIndices chi T exceptional)
          (fun p => norm ((1 : Complex) / symmetricCompletedZeroValue p)) := by
  have hxReal : (1 : Real) <= (x : Real) := by
    have hRaw : ((1 : Nat) : Real) <= (x : Real) := (Nat.cast_le).2 hx
    simpa only [Nat.cast_one] using hRaw
  have hTerm (p : SymmetricCompletedZeroIndex chi) :
      norm ((x : Complex) ^ symmetricCompletedZeroValue p /
          symmetricCompletedZeroValue p) <=
        (x : Real) * norm ((1 : Complex) / symmetricCompletedZeroValue p) := by
    have hRe := symmetricCompletedZeroValue_re_mem_Ioo hchi hPrimitive p
    have h := BombieriVinogradov.ComplexAnalysis.norm_real_cpow_div_le_mul_norm_one_div
      hxReal hRe.2.le
    simpa only [Complex.ofReal_natCast] using h
  rw [truncatedCriticalZeroSum_eq_sum_symmetricCompletedZeroValue]
  calc
    norm (Finset.sum (retainedCriticalZeroIndices chi T exceptional)
      (fun p => (x : Complex) ^ symmetricCompletedZeroValue p /
        symmetricCompletedZeroValue p)) <=
      Finset.sum (retainedCriticalZeroIndices chi T exceptional)
        (fun p => norm ((x : Complex) ^ symmetricCompletedZeroValue p /
          symmetricCompletedZeroValue p)) := norm_sum_le _ _
    _ <= Finset.sum (retainedCriticalZeroIndices chi T exceptional)
        (fun p => (x : Real) *
          norm ((1 : Complex) / symmetricCompletedZeroValue p)) :=
      Finset.sum_le_sum (fun p _ => hTerm p)
    _ = (x : Real) *
        Finset.sum (retainedCriticalZeroIndices chi T exceptional)
          (fun p => norm ((1 : Complex) / symmetricCompletedZeroValue p)) :=
      (Finset.mul_sum (retainedCriticalZeroIndices chi T exceptional)
        (fun p => norm ((1 : Complex) / symmetricCompletedZeroValue p))
        (x : Real)).symm

end BombieriVinogradov.SiegelWalfisz
