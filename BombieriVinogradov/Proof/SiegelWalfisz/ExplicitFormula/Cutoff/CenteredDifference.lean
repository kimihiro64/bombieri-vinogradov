import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Centered.ZeroSum
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Cutoff.ASCIIExpansion
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Cutoff.DifferenceIndices
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Cutoff.RetainedMonotone
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring

/-!
# Centered retained-zero cutoff difference

This module writes the centered retained-zero sum change over exactly the newly retained indices.
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

theorem centeredTruncatedCriticalZeroSum_sub_eq_sum_cutoffDifference
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N)
    (x : Nat) {T Tprime : Real} (hCutoff : T <= Tprime)
    (exceptional : Option Complex) :
    centeredTruncatedCriticalZeroSum chi x Tprime exceptional -
        centeredTruncatedCriticalZeroSum chi x T exceptional =
      Finset.sum
        (retainedCriticalZeroCutoffDifference chi T Tprime exceptional)
        (fun p =>
          ((x : Complex) ^ symmetricCompletedZeroValue p - 1) /
            symmetricCompletedZeroValue p) := by
  classical
  let small := retainedCriticalZeroIndices chi T exceptional
  let large := retainedCriticalZeroIndices chi Tprime exceptional
  let diff := retainedCriticalZeroCutoffDifference chi T Tprime exceptional
  let rho : SymmetricCompletedZeroIndex chi -> Complex :=
    fun p => symmetricCompletedZeroValue p
  let fx : SymmetricCompletedZeroIndex chi -> Complex :=
    fun p => (x : Complex) ^ rho p / rho p
  let fone : SymmetricCompletedZeroIndex chi -> Complex :=
    fun p => (1 : Complex) ^ rho p / rho p
  let centered : SymmetricCompletedZeroIndex chi -> Complex :=
    fun p => ((x : Complex) ^ rho p - 1) / rho p
  have hSubset : small <= large := by
    simpa [small, large] using
      retainedCriticalZeroIndices_mono hCutoff exceptional
  have hDiff : large \ small = diff := by
    apply Finset.ext
    intro p
    rw [Finset.mem_sdiff]
    change
      And
          ((retainedCriticalZeroIndices chi Tprime exceptional :
            Set (SymmetricCompletedZeroIndex chi)) p)
          (Not ((retainedCriticalZeroIndices chi T exceptional :
            Set (SymmetricCompletedZeroIndex chi)) p)) <->
        (retainedCriticalZeroCutoffDifference chi T Tprime exceptional :
          Set (SymmetricCompletedZeroIndex chi)) p
    exact mem_retainedCriticalZeroCutoffDifference_iff.symm
  have hDifferenceSum
      (f : SymmetricCompletedZeroIndex chi -> Complex) :
      Finset.sum large f - Finset.sum small f =
        Finset.sum diff f := by
    have hSum :
        Finset.sum (large \ small) f + Finset.sum small f =
          Finset.sum large f :=
      Finset.sum_sdiff hSubset
    calc
      Finset.sum large f - Finset.sum small f =
          (Finset.sum (large \ small) f + Finset.sum small f) -
            Finset.sum small f := by rw [hSum]
      _ = Finset.sum (large \ small) f := by ring
      _ = Finset.sum diff f := by rw [hDiff]
  have hLargeX :
      truncatedCriticalZeroSum chi x Tprime exceptional =
        Finset.sum large fx := by
    simpa [large, fx, rho] using
      truncatedCriticalZeroSum_eq_sum_symmetricCompletedZeroValue
        chi x Tprime exceptional
  have hSmallX :
      truncatedCriticalZeroSum chi x T exceptional =
        Finset.sum small fx := by
    simpa [small, fx, rho] using
      truncatedCriticalZeroSum_eq_sum_symmetricCompletedZeroValue
        chi x T exceptional
  have hLargeOne :
      truncatedCriticalZeroSum chi 1 Tprime exceptional =
        Finset.sum large fone := by
    simpa [large, fone, rho] using
      truncatedCriticalZeroSum_eq_sum_symmetricCompletedZeroValue
        chi 1 Tprime exceptional
  have hSmallOne :
      truncatedCriticalZeroSum chi 1 T exceptional =
        Finset.sum small fone := by
    simpa [small, fone, rho] using
      truncatedCriticalZeroSum_eq_sum_symmetricCompletedZeroValue
        chi 1 T exceptional
  have hCenteredTerm (p : SymmetricCompletedZeroIndex chi) :
      centered p = fx p - fone p := by
    simp [centered, fx, fone, rho]
    ring
  have hCenteredSum :
      Finset.sum diff centered =
        Finset.sum diff fx - Finset.sum diff fone := by
    calc
      Finset.sum diff centered =
          Finset.sum diff (fun p => fx p - fone p) :=
        Finset.sum_congr rfl fun p hp => hCenteredTerm p
      _ = Finset.sum diff fx - Finset.sum diff fone := by
        simpa only using (Finset.sum_sub_distrib (s := diff) fx fone)
  unfold centeredTruncatedCriticalZeroSum
  rw [hLargeX, hSmallX, hLargeOne, hSmallOne]
  change
    (Finset.sum large fx - Finset.sum large fone) -
        (Finset.sum small fx - Finset.sum small fone) =
      Finset.sum diff centered
  rw [hCenteredSum, (hDifferenceSum fx).symm, (hDifferenceSum fone).symm]
  ring

end BombieriVinogradov.SiegelWalfisz
