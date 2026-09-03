import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Horizontal.ZeroHeightWindowCountBound
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# Summability of the near-zero reciprocal series

This module isolates the finite-support argument showing that the reciprocal
series restricted to an open unit zero-height window is summable.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem summable_nearZero_reciprocal
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : Ne chi 1) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    (T : Real) (s : Complex) :
    Summable (fun p : SymmetricCompletedZeroIndex chi =>
      if abs (T - (symmetricCompletedZeroValue p).im) < 1 then
        1 / (s - symmetricCompletedZeroValue p)
      else 0) := by
  let nearTarget : SymmetricCompletedZeroIndex chi -> Complex := fun p =>
    if abs (T - (symmetricCompletedZeroValue p).im) < 1 then
      1 / (s - symmetricCompletedZeroValue p)
    else 0
  have hWindowFinite :
      Set.Finite (zeroHeightWindow (chi := chi) T) :=
    finite_zeroHeightWindow hchi hPrimitive T
  have hSupportFinite : Set.Finite (Function.support nearTarget) := by
    refine hWindowFinite.subset ?_
    intro p hpSupport
    change abs (T - (symmetricCompletedZeroValue p).im) < 1
    by_contra hpNotNear
    apply hpSupport
    dsimp [nearTarget]
    rw [if_neg hpNotNear]
  simpa [nearTarget] using summable_of_hasFiniteSupport hSupportFinite

end BombieriVinogradov.SiegelWalfisz
