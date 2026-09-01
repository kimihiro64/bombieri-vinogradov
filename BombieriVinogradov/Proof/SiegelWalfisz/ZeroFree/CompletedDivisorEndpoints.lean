import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedHadamardNoMonomial
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedOriginNonvanishing
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedZeroSummability
import PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.Divisor

/-!
# Endpoint exclusion from the completed-function zero divisor

This module proves that one is not represented by the multiplicity-aware nonzero-zero
divisor of a primitive nonprincipal symmetric completed Dirichlet L-function.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem symmetricCompletedLFunction_one_ne_divisorZeroIndex₀_val
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : chi ≠ 1) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    (p : Complex.Hadamard.divisorZeroIndex₀
      (symmetricCompletedLFunction chi) (Set.univ : Set Complex)) :
    (1 : Complex) ≠ Complex.Hadamard.divisorZeroIndex₀_val p := by
  intro hOne
  have hProductAtIndex :=
    Complex.Hadamard.divisorCanonicalProduct_eq_zero_at_index
      1 (symmetricCompletedLFunction chi)
      (summable_symmetricCompletedLFunction_divisorZeroIndex₀_norm_inv_sq
        hchi hPrimitive) p
  rw [← hOne] at hProductAtIndex
  choose P _hDegree hFactorization using
    symmetricCompletedLFunction_hadamard_factorization_no_monomial hchi hPrimitive
  have hFunctionOne := hFactorization 1
  rw [hProductAtIndex, mul_zero] at hFunctionOne
  exact symmetricCompletedLFunction_one_ne_zero hchi hFunctionOne

end BombieriVinogradov.SiegelWalfisz
