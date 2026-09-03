import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Cutoff.CenteredDifference
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Cutoff.CenteredZeroTermBound
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Normed.Group.Basic

/-!
# Norm aggregation for the centered cutoff difference

This module combines the exact finite difference identity with the pointwise
centered-zero majorant, retaining the difference cardinality explicitly.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem norm_centeredTruncatedCriticalZeroSum_sub_le_card_mul
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N)
    {x : Nat} (hx : 2 < x) {T Tprime : Real}
    (hT : 2 <= T) (hCutoff : T <= Tprime)
    (exceptional : Option Complex) :
    norm
        (centeredTruncatedCriticalZeroSum chi x Tprime exceptional -
          centeredTruncatedCriticalZeroSum chi x T exceptional) <=
      ((retainedCriticalZeroCutoffDifference
          chi T Tprime exceptional).card : Real) *
        (4 * (x : Real) / T) := by
  let diff :=
    retainedCriticalZeroCutoffDifference chi T Tprime exceptional
  let term : SymmetricCompletedZeroIndex chi -> Complex :=
    fun p =>
      ((x : Complex) ^ symmetricCompletedZeroValue p - 1) /
        symmetricCompletedZeroValue p
  rw [
    centeredTruncatedCriticalZeroSum_sub_eq_sum_cutoffDifference
      chi x hCutoff exceptional
  ]
  change
    norm (Finset.sum diff term) <=
      (diff.card : Real) * (4 * (x : Real) / T)
  calc
    norm (Finset.sum diff term) <=
        Finset.sum diff (fun p => norm (term p)) :=
      norm_sum_le diff term
    _ <= Finset.sum diff (fun _ => 4 * (x : Real) / T) :=
      Finset.sum_le_sum (fun p hp => by
        have hpSet :
            (diff : Set (SymmetricCompletedZeroIndex chi)) p := hp
        simpa [diff, term] using
          norm_centeredZeroTerm_of_mem_cutoffDifference_le
            (x := x) hx (T := T) (Tprime := Tprime) hT
            (exceptional := exceptional) hpSet)
    _ = (diff.card : Real) * (4 * (x : Real) / T) := by
      simp

end BombieriVinogradov.SiegelWalfisz
