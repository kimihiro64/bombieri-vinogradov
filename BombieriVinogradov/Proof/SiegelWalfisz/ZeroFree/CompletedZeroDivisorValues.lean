import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedHadamardNoMonomial
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedZeroIndex
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedZeroSummability
import PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.Divisor

/-!
# Values represented by the completed-function zero divisor

This module proves that every multiplicity-aware divisor index evaluates to an actual
zero of the primitive symmetric completed Dirichlet L-function.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem symmetricCompletedLFunction_divisorZeroIndex₀_apply_eq_zero
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : chi ≠ 1) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    (p : SymmetricCompletedZeroIndex chi) :
    symmetricCompletedLFunction chi
        (Complex.Hadamard.divisorZeroIndex₀_val p) = 0 := by
  have hProductAtIndex :=
    Complex.Hadamard.divisorCanonicalProduct_eq_zero_at_index
      1 (symmetricCompletedLFunction chi)
      (summable_symmetricCompletedLFunction_divisorZeroIndex₀_norm_inv_sq
        hchi hPrimitive) p
  choose P _hDegree hFactorization using
    symmetricCompletedLFunction_hadamard_factorization_no_monomial hchi hPrimitive
  have hValue :=
    hFactorization (Complex.Hadamard.divisorZeroIndex₀_val p)
  rw [hProductAtIndex, mul_zero] at hValue
  exact hValue

end BombieriVinogradov.SiegelWalfisz
