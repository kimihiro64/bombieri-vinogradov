import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedNormalization
import PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.DivisorIndex

/-!
# Multiplicity-aware zero index for a symmetric completed L-function

This module provides the narrow shared type alias used by zero-divisor consumers.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

abbrev SymmetricCompletedZeroIndex
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N) :=
  Complex.Hadamard.divisorZeroIndex₀
    (symmetricCompletedLFunction chi) (Set.univ : Set Complex)

end BombieriVinogradov.SiegelWalfisz
