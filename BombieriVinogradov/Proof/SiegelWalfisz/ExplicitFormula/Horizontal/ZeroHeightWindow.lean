import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedZeroIndex
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedZeroValue

/-!
# Unit vertical windows for completed zeros

This module owns only the set of multiplicity-indexed completed zeros whose
ordinates lie within one unit of a prescribed real height.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

/-- Completed zeros, counted with divisor multiplicity, whose ordinates lie
within one unit of the real height T. -/
def zeroHeightWindow
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (T : Real) : Set (SymmetricCompletedZeroIndex chi) :=
  {p | abs (T - (symmetricCompletedZeroValue p).im) < 1}

end BombieriVinogradov.SiegelWalfisz
