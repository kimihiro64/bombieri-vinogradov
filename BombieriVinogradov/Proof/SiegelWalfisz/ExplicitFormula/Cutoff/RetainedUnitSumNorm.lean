import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Cutoff.ASCIIExpansion
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.RetainedZeroValues
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedZeroIndex
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedZeroValue
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.DirichletCharacter.Basic

/-!
# Norm bound for the retained zero sum at one
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

theorem norm_truncatedCriticalZeroSum_one_le_sum_norm_one_div
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N)
    (T : Real) (exceptional : Option Complex) :
    norm (truncatedCriticalZeroSum chi 1 T exceptional) <=
      Finset.sum (retainedCriticalZeroIndices chi T exceptional)
        (fun p => norm (1 / symmetricCompletedZeroValue p)) := by
  rw [truncatedCriticalZeroSum_eq_sum_symmetricCompletedZeroValue]
  calc
    norm
        (Finset.sum (retainedCriticalZeroIndices chi T exceptional)
          (fun p =>
            ((1 : Nat) : Complex) ^ symmetricCompletedZeroValue p /
              symmetricCompletedZeroValue p)) <=
      Finset.sum (retainedCriticalZeroIndices chi T exceptional)
        (fun p => norm
          (((1 : Nat) : Complex) ^ symmetricCompletedZeroValue p /
            symmetricCompletedZeroValue p)) :=
      norm_sum_le _ _
    _ = Finset.sum (retainedCriticalZeroIndices chi T exceptional)
        (fun p => norm (1 / symmetricCompletedZeroValue p)) := by
      apply Finset.sum_congr rfl
      intro p hp
      simp

end BombieriVinogradov.SiegelWalfisz
