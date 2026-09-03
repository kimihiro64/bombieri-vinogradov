import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.RetainedZeroValues
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedZeroValue
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# ASCII retained-zero sum expansion

This module restates the multiplicity-indexed retained-zero sum through the
public ASCII completed-zero value interface.
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

theorem truncatedCriticalZeroSum_eq_sum_symmetricCompletedZeroValue
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N)
    (x : Nat) (T : Real) (exceptional : Option Complex) :
    truncatedCriticalZeroSum chi x T exceptional =
      Finset.sum (retainedCriticalZeroIndices chi T exceptional)
        (fun p =>
          (x : Complex) ^ symmetricCompletedZeroValue p /
            symmetricCompletedZeroValue p) := by
  simpa [symmetricCompletedZeroValue] using
    truncatedCriticalZeroSum_eq_sum_retainedCriticalZeroIndices
      chi x T exceptional

end BombieriVinogradov.SiegelWalfisz
