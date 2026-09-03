import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedZeroCanonicalTermSummable
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-!
# Summability of two-point completed-zero reciprocal differences

This module cancels the common genus-one correction between two canonical
zero series, yielding a reusable summability theorem for reciprocal differences.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem summable_completedZero_reciprocalDifference
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : Ne chi 1) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    {s w : Complex}
    (hsAway : forall p : SymmetricCompletedZeroIndex chi,
      Ne s (symmetricCompletedZeroValue p))
    (hwAway : forall p : SymmetricCompletedZeroIndex chi,
      Ne w (symmetricCompletedZeroValue p)) :
    Summable (fun p : SymmetricCompletedZeroIndex chi =>
      1 / (s - symmetricCompletedZeroValue p) -
        1 / (w - symmetricCompletedZeroValue p)) := by
  have hsCanonical :=
    summable_completedZero_canonicalTerm hchi hPrimitive hsAway
  have hwCanonical :=
    summable_completedZero_canonicalTerm hchi hPrimitive hwAway
  have hDifference := hsCanonical.sub hwCanonical
  refine hDifference.congr ?_
  intro p
  ring

end BombieriVinogradov.SiegelWalfisz
