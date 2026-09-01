import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedHadamardFactorization
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedOriginNonvanishing

/-!
# Hadamard factorization without an origin monomial

This module uses completed-function nonvanishing at zero to remove the origin power from
the genus-one divisor canonical product.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem analyticOrderNatAt_symmetricCompletedLFunction_zero
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : chi ≠ 1) (hPrimitive : DirichletCharacter.IsPrimitive chi) :
    analyticOrderNatAt (symmetricCompletedLFunction chi) 0 = 0 := by
  rw [analyticOrderNatAt,
    analyticOrderAt_eq_zero.mpr (.inr
      (symmetricCompletedLFunction_zero_ne_zero hchi hPrimitive))]
  rfl

theorem symmetricCompletedLFunction_hadamard_factorization_no_monomial
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : chi ≠ 1) (hPrimitive : DirichletCharacter.IsPrimitive chi) :
    exists P : Polynomial Complex,
      P.degree ≤ 1 ∧ forall z : Complex,
        symmetricCompletedLFunction chi z =
          Complex.exp (Polynomial.eval z P) *
            Complex.Hadamard.divisorCanonicalProduct 1
              (symmetricCompletedLFunction chi) (Set.univ : Set Complex) z := by
  obtain ⟨P, hDegree, hFactorization⟩ :=
    symmetricCompletedLFunction_hadamard_factorization hchi hPrimitive
  refine ⟨P, hDegree, ?_⟩
  intro z
  simpa [analyticOrderNatAt_symmetricCompletedLFunction_zero hchi hPrimitive,
    mul_assoc] using hFactorization z

end BombieriVinogradov.SiegelWalfisz
