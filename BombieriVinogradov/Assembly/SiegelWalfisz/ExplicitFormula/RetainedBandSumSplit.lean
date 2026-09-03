import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Cutoff.RetainedBandSum
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Cutoff.RetainedZeroBand
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.RetainedZeroValues
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedZeroIndex
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedZeroValue
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Range
import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.DirichletCharacter.Basic

/-!
# Exact split of the retained reciprocal-zero sum
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

theorem sum_norm_one_div_retainedCriticalZeroIndices_eq_bands
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    {T : Real} (hT : 0 < T) (exceptional : Option Complex) :
    Finset.sum (retainedCriticalZeroIndices chi T exceptional)
        (fun p => norm (1 / symmetricCompletedZeroValue p)) =
      Finset.sum (retainedCriticalZeroBand chi T exceptional 0)
          (fun p => norm (1 / symmetricCompletedZeroValue p)) +
        Finset.sum (Finset.Ico 1 (Nat.ceil T)) (fun k =>
          Finset.sum (retainedCriticalZeroBand chi T exceptional k)
            (fun p => norm (1 / symmetricCompletedZeroValue p))) := by
  classical
  let f : SymmetricCompletedZeroIndex chi -> Real := fun p =>
    norm (1 / symmetricCompletedZeroValue p)
  let g : Nat -> Real := fun k =>
    Finset.sum (retainedCriticalZeroBand chi T exceptional k) f
  have hBands :
      Finset.sum (Finset.range (Nat.ceil T)) g =
        Finset.sum (retainedCriticalZeroIndices chi T exceptional) f := by
    exact sum_retainedCriticalZeroBands_eq hT exceptional f
  have hCeilPos : 0 < Nat.ceil T := (Nat.ceil_pos).2 hT
  calc
    Finset.sum (retainedCriticalZeroIndices chi T exceptional)
        (fun p => norm (1 / symmetricCompletedZeroValue p)) =
      Finset.sum (Finset.range (Nat.ceil T)) g := by
        simpa only [f] using hBands.symm
    _ = Finset.sum (Finset.Ico 0 (Nat.ceil T)) g := by
      rw [Finset.range_eq_Ico]
    _ = g 0 + Finset.sum (Finset.Ico 1 (Nat.ceil T)) g := by
      simpa using Finset.sum_eq_sum_Ico_succ_bot hCeilPos g
    _ = Finset.sum (retainedCriticalZeroBand chi T exceptional 0)
          (fun p => norm (1 / symmetricCompletedZeroValue p)) +
        Finset.sum (Finset.Ico 1 (Nat.ceil T)) (fun k =>
          Finset.sum (retainedCriticalZeroBand chi T exceptional k)
            (fun p => norm (1 / symmetricCompletedZeroValue p))) := by
      rfl

end BombieriVinogradov.SiegelWalfisz
