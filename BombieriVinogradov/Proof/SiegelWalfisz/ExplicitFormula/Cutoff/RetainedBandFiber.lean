import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Cutoff.RetainedZeroBand
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Cutoff.RetainedZeroBandCover
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.RetainedZeroValues
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedZeroIndex
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedZeroValue
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Defs
import Mathlib.NumberTheory.DirichletCharacter.Basic

/-!
# Retained zero bands as canonical index fibers

This module identifies each absolute-height band with the corresponding
fiber of the floor-height index on the retained cutoff.
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

theorem filter_retainedCriticalZeroIndices_bandIndex_eq
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (T : Real) (exceptional : Option Complex) (k : Nat) :
    (retainedCriticalZeroIndices chi T exceptional).filter
        (fun p => retainedCriticalZeroBandIndex p = k) =
      retainedCriticalZeroBand chi T exceptional k := by
  classical
  apply Finset.ext
  intro p
  rw [Finset.mem_filter]
  exact Iff.intro
    (fun hp => by
      have hpSet :
          (retainedCriticalZeroIndices chi T exceptional :
            Set (SymmetricCompletedZeroIndex chi)) p := hp.1
      have hCanonical := mem_retainedCriticalZeroBand_bandIndex hpSet
      have hCanonicalData :=
        (mem_retainedCriticalZeroBand_iff).mp hCanonical
      unfold retainedCriticalZeroBand
      exact Finset.mem_filter.mpr
        (And.intro hp.1 (by simpa [hp.2] using hCanonicalData.2)))
    (fun hp => by
      unfold retainedCriticalZeroBand at hp
      have hData := Finset.mem_filter.mp hp
      have hIndex : retainedCriticalZeroBandIndex p = k := by
        unfold retainedCriticalZeroBandIndex
        apply (Nat.floor_eq_iff
          (abs_nonneg (symmetricCompletedZeroValue p).im)).2
        exact And.intro hData.2.1
          (by
            simpa only [Nat.cast_add, Nat.cast_one] using hData.2.2)
      exact And.intro hData.1 hIndex)

end BombieriVinogradov.SiegelWalfisz
