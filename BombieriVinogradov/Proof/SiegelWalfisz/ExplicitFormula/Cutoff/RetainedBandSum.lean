import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Cutoff.RetainedBandFiber
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Cutoff.RetainedZeroBand
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Cutoff.RetainedZeroBandCover
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.RetainedZeroValues
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedZeroIndex
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Range
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Defs
import Mathlib.NumberTheory.DirichletCharacter.Basic

/-!
# Fiberwise sums over retained zero bands

This module partitions a retained zero cutoff by the canonical floor-height
index and sums any additive-valued function exactly over those fibers.
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

theorem sum_retainedCriticalZeroBands_eq
    {M : Type} [AddCommMonoid M]
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    {T : Real} (hT : 0 < T) (exceptional : Option Complex)
    (f : SymmetricCompletedZeroIndex chi -> M) :
    Finset.sum (Finset.range (Nat.ceil T)) (fun k =>
        Finset.sum (retainedCriticalZeroBand chi T exceptional k) f) =
      Finset.sum (retainedCriticalZeroIndices chi T exceptional) f := by
  classical
  calc
    Finset.sum (Finset.range (Nat.ceil T)) (fun k =>
        Finset.sum (retainedCriticalZeroBand chi T exceptional k) f) =
      Finset.sum (Finset.range (Nat.ceil T)) (fun k =>
        Finset.sum ((retainedCriticalZeroIndices chi T exceptional).filter
          (fun p => retainedCriticalZeroBandIndex p = k)) f) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [filter_retainedCriticalZeroIndices_bandIndex_eq]
    _ = Finset.sum (retainedCriticalZeroIndices chi T exceptional) f := by
      apply Finset.sum_fiberwise_of_maps_to
      intro p hp
      apply Finset.mem_range.mpr
      have hpSet :
          (retainedCriticalZeroIndices chi T exceptional :
            Set (SymmetricCompletedZeroIndex chi)) p := hp
      exact retainedCriticalZeroBandIndex_lt_ceil hT hpSet

end BombieriVinogradov.SiegelWalfisz
