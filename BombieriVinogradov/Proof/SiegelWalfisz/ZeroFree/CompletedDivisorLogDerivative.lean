import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedZeroSummability
import PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.Divisor
import PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.DivisorConvergence

/-!
# Logarithmic derivative of the completed-function divisor product

This module proves summability of the zero terms away from the divisor and identifies
their sum with the logarithmic derivative of the genus-one canonical product.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem summable_symmetricCompletedLFunction_logDerivTerms_divisorZeroIndex₀
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : chi ≠ 1) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    {z : Complex}
    (hz : forall p : Complex.Hadamard.divisorZeroIndex₀
        (symmetricCompletedLFunction chi) (Set.univ : Set Complex),
      z ≠ Complex.Hadamard.divisorZeroIndex₀_val p) :
    Summable
      (fun p : Complex.Hadamard.divisorZeroIndex₀
          (symmetricCompletedLFunction chi) (Set.univ : Set Complex) =>
        1 / (z - Complex.Hadamard.divisorZeroIndex₀_val p) +
          1 / Complex.Hadamard.divisorZeroIndex₀_val p) :=
  Complex.Hadamard.summable_logDerivTerms_divisorZeroIndex₀_of_summable_inv_sq
    (summable_symmetricCompletedLFunction_divisorZeroIndex₀_norm_inv_sq hchi hPrimitive) hz

theorem logDeriv_symmetricCompletedLFunction_divisorCanonicalProduct_one_eq_tsum
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : chi ≠ 1) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    {z : Complex}
    (hz : forall p : Complex.Hadamard.divisorZeroIndex₀
        (symmetricCompletedLFunction chi) (Set.univ : Set Complex),
      z ≠ Complex.Hadamard.divisorZeroIndex₀_val p) :
    logDeriv
        (Complex.Hadamard.divisorCanonicalProduct 1
          (symmetricCompletedLFunction chi) (Set.univ : Set Complex)) z =
      ∑' p : Complex.Hadamard.divisorZeroIndex₀
          (symmetricCompletedLFunction chi) (Set.univ : Set Complex),
        (1 / (z - Complex.Hadamard.divisorZeroIndex₀_val p) +
          1 / Complex.Hadamard.divisorZeroIndex₀_val p) :=
  Complex.Hadamard.logDeriv_divisorCanonicalProduct_one_eq_tsum_of_forall_ne
    (summable_symmetricCompletedLFunction_divisorZeroIndex₀_norm_inv_sq hchi hPrimitive) hz

end BombieriVinogradov.SiegelWalfisz
